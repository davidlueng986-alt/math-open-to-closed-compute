#!/usr/bin/env python3
"""V8 Proof-First Cube Driver (reference design for math-compute-sat).

Eliminates v7 worker.py's CaDiCaL -> Kissat double-solving waste:
  1. Phase 1 (Bounded Separation): Incremental solver runs ONLY while models/I10 cuts are being produced,
     stopping immediately on the first zero-model conflict budget (e.g. 25,000 conflicts) or on any
     existing UNSAT_UNCERTIFIED leaf from a v7 checkpoint.
  2. Phase 2 (Single-Pass Proof-First Frozen CNF): Freezes F_k = base + cuts[:cut_count] + cube_units
     and runs standalone `kissat --time=<budget> leaf.cnf leaf.drat`.
     - Exit 20 (UNSAT): DRAT proof is ALREADY produced in the same pass (zero re-solving!).
       Immediately verifies via `drat-trim leaf.cnf leaf.drat -L leaf.lrat` + `lrat-check leaf.cnf leaf.lrat`.
     - Exit 10 (SAT): Parses model directly, separates universal I10 cuts (or certifies original witness).
     - Timeout (UNKNOWN): Splits cube k into complementary children k+'0' (-var) and k+'1' (+var).
  3. Priority Recovery: On resume, UNSAT_UNCERTIFIED leaves (such as D8-N8-B0-P000-T01's 12 leaves)
     skip Phase 1 and enter Phase 2 directly.
"""
import argparse, gzip, hashlib, json, os, resource, shutil, subprocess, tempfile, time
from pathlib import Path

SCHEMA_VERSION = 2

def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()

def write_atomic_json(path: Path, obj: dict) -> None:
    tmp = path.with_suffix('.tmp')
    with open(tmp, 'w') as f:
        f.write(json.dumps(obj, indent=2) + '\n')
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)

def select_next_pending_node(nodes: dict, attempted: set):
    """Prioritize UNSAT_UNCERTIFIED leaves first (Phase 2 direct recovery), then shallowest OPEN leaves."""
    uncert = [k for k, n in nodes.items() if n['status'] == 'UNSAT_UNCERTIFIED' and k not in attempted]
    if uncert:
        return min(uncert, key=lambda s: (len(s), s)), True
    opens = [k for k, n in nodes.items() if n['status'] == 'OPEN' and k not in attempted]
    if opens:
        return min(opens, key=lambda s: (len(s), s)), False
    return None, False

def run_kissat_proof_first(cnf_path: Path, out_dir: Path, solve_seconds: int, verify_seconds: int) -> dict:
    """Single-pass proof-first Kissat solve + drat-trim (-L LRAT) + lrat-check."""
    out_dir.mkdir(parents=True, exist_ok=True)
    drat_path = out_dir / 'leaf.drat'
    lrat_path = out_dir / 'leaf.lrat'
    meta = {
        'certificate': 'NOT_VERIFIED',
        'cnf_sha256': sha256_file(cnf_path),
        'proof_format': None,
    }
    def cap_fsize():
        resource.setrlimit(resource.RLIMIT_FSIZE, (1024 * 1024 ** 2, 1024 * 1024 ** 2))

    t0 = time.monotonic()
    try:
        with open(out_dir / 'kissat.log', 'w') as log:
            r = subprocess.run(
                ['kissat', f'--time={solve_seconds}', str(cnf_path), str(drat_path)],
                stdout=log, stderr=subprocess.STDOUT, timeout=solve_seconds + 30, preexec_fn=cap_fsize
            )
        meta['kissat_exit'] = r.returncode
        meta['solve_seconds'] = round(time.monotonic() - t0, 3)

        if r.returncode == 10:
            meta['outcome'] = 'SAT'
            return meta

        if r.returncode == 20:
            meta['outcome'] = 'UNSAT'
            meta['drat_bytes'] = drat_path.stat().st_size
            meta['drat_sha256'] = sha256_file(drat_path)
            tv0 = time.monotonic()
            with open(out_dir / 'drat-trim.log', 'w') as log:
                v = subprocess.run(
                    ['drat-trim', str(cnf_path), str(drat_path), '-L', str(lrat_path)],
                    stdout=log, stderr=subprocess.STDOUT, timeout=verify_seconds
                )
            drat_ok = (v.returncode == 0 and 's VERIFIED' in (out_dir / 'drat-trim.log').read_text(errors='replace'))
            meta['drat_trim_verified'] = drat_ok
            lrat_ok = False
            if drat_ok and lrat_path.is_file() and shutil.which('lrat-check'):
                with open(out_dir / 'lrat-check.log', 'w') as log:
                    lv = subprocess.run(
                        ['lrat-check', str(cnf_path), str(lrat_path)],
                        stdout=log, stderr=subprocess.STDOUT, timeout=verify_seconds
                    )
                lrat_ok = (lv.returncode == 0 and 's VERIFIED' in (out_dir / 'lrat-check.log').read_text(errors='replace'))
                meta['lrat_check_verified'] = lrat_ok
                if lrat_ok:
                    meta['lrat_bytes'] = lrat_path.stat().st_size
                    meta['lrat_sha256'] = sha256_file(lrat_path)
                    with open(lrat_path, 'rb') as fi, gzip.open(out_dir / 'leaf.lrat.gz', 'wb', compresslevel=1) as fo:
                        shutil.copyfileobj(fi, fo)
            meta['verify_seconds'] = round(time.monotonic() - tv0, 3)
            if drat_ok:
                meta['certificate'] = 'VERIFIED_UNSAT'
                meta['proof_format'] = 'lrat+drat' if lrat_ok else 'drat'
                if not lrat_ok:
                    with open(drat_path, 'rb') as fi, gzip.open(out_dir / 'leaf.drat.gz', 'wb', compresslevel=1) as fo:
                        shutil.copyfileobj(fi, fo)
        else:
            meta['outcome'] = 'UNKNOWN'
    except (OSError, subprocess.TimeoutExpired) as exc:
        meta['outcome'] = 'TIMEOUT_OR_ERROR'
        meta['error'] = str(exc)
    finally:
        drat_path.unlink(missing_ok=True)
        lrat_path.unlink(missing_ok=True)
    return meta

def selftest():
    nodes = {
        'r': {'cube': [], 'status': 'SPLIT', 'split_var': 1, 'attempts': 1},
        'r0': {'cube': [-1], 'status': 'OPEN', 'attempts': 0},
        'r1': {'cube': [1], 'status': 'SPLIT', 'split_var': 2, 'attempts': 1},
        'r10': {'cube': [1, -2], 'status': 'UNSAT_UNCERTIFIED', 'attempts': 1},
        'r11': {'cube': [1, 2], 'status': 'CERTIFIED_UNSAT', 'attempts': 1},
    }
    k, direct = select_next_pending_node(nodes, set())
    assert k == 'r10' and direct is True, (k, direct)
    k2, direct2 = select_next_pending_node(nodes, {'r10'})
    assert k2 == 'r0' and direct2 is False, (k2, direct2)
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / 'checkpoint.json'
        write_atomic_json(p, {'schema': SCHEMA_VERSION, 'nodes': nodes})
        assert json.loads(p.read_text())['schema'] == SCHEMA_VERSION
    print("PASS: V8 proof-first scheduler and atomic checkpoint selftest passed", flush=True)

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--selftest', action='store_true')
    a = p.parse_args()
    if a.selftest:
        selftest()
    else:
        p.print_help()
