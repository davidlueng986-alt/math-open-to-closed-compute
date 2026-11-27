#!/usr/bin/env python3
"""Lean-CNF V8 CEGAR + Proof-First Kissat/DRAT/LRAT runner for D678 tasks."""
import argparse, gzip, hashlib, itertools, json, random, resource, shutil, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'ramsey-r310-v8-agent3-encoding'))
import lean_cnf_sms as lc
from pysat.solvers import Solver

N = 40

def bits(x):
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b

def independent(adj, verts, k, limit=256, rng=None):
    order = list(verts)
    if rng:
        rng.shuffle(order)
    inv = {v: i for i, v in enumerate(order)}
    b = [sum(1 << inv[j] for j in bits(adj[v]) if j in inv) for v in order]
    count = 0
    def go(p, rem, s):
        nonlocal count
        if count >= limit:
            return
        if rem == 0:
            count += 1
            yield tuple(sorted(s))
            return
        while p.bit_count() >= rem and count < limit:
            x = p & -p
            p ^= x
            i = x.bit_length() - 1
            yield from go(p & ~b[i], rem - 1, s + [order[i]])
    yield from go((1 << len(order)) - 1, k, [])

def sha256_file(p: Path):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

def run_task(task, out_dir: Path, seconds: int, proof_seconds: int):
    out_dir.mkdir(parents=True, exist_ok=True)
    z, meta = lc.build_lean_cnf(task, sym_mode='static_lex')
    if meta.get('unsat_by_prefilter'):
        res = {'task': task['id'], 'status': 'UNSAT_BY_V8_KONIG_PREFILTER', 'meta': meta}
        (out_dir / 'result.json').write_text(json.dumps(res, indent=2) + '\n')
        print(json.dumps(res), flush=True)
        return

    d, q = task['d'], task['q']
    X = list(range(2, d + 1))
    Y = list(range(d + 1, d + q))
    T = list(range(d + q, N))
    H0 = Y + T
    H1 = X + T

    base_clauses = list(z.clauses)
    extra_cuts = []
    seen_cuts = set()
    rng = random.Random(int(task['key'][:12], 16))
    t0 = time.monotonic()
    models = 0
    codeg_cuts = 0
    i10_cuts = 0
    status = 'OPEN'

    with Solver(name='cadical195', bootstrap_with=base_clauses) as sol:
        while time.monotonic() - t0 < seconds:
            sol.conf_budget(50000)
            r = sol.solve_limited()
            if r is None:
                continue
            if r is False:
                status = 'UNSAT_PENDING_PROOF'
                break
            model = sol.get_model()
            pos = {x for x in model if 1 <= x <= 780}
            adj = [0] * N
            for (i, j), v in lc.edge.items():
                if v in pos:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
            models += 1
            added = 0

            # 1. Lazy non-edge codegree & saturation separation
            for i in range(N):
                di = adj[i].bit_count()
                for j in range(i + 1, N):
                    if (adj[i] >> j) & 1:
                        continue
                    dj = adj[j].bit_count()
                    common = adj[i] & adj[j]
                    c = common.bit_count()
                    if c == 0:
                        # saturation violation: must have edge or a common neighbor? Actually add I10 directly if needed,
                        # or force edge(i,j) OR some common neighbor? Skip non-universal; I10 check catches it!
                        pass
                    cap = di + dj - 11
                    if c > cap:
                        # Sound I10? No, nonedge codegree > di+dj-11 means common non-neighbors <= 27 is violated,
                        # Wait: only add genuine I10 cuts so every added clause is 100% universally valid!
                        pass

            # 2. Fast exact I9-in-H0, I9-in-H1, and I10-in-G separation (100% universally valid cuts!)
            bad = set()
            for verts, k2, prefix, lim in ((H0, 9, (0,), 256), (H1, 9, (1,), 256), (range(N), 10, (), 512)):
                for ss in independent(adj, verts, k2, lim, rng):
                    bad.add(tuple(sorted(prefix + ss)))
            if not bad:
                assert not list(independent(adj, range(N), 10, 1))
                wp = out_dir / 'witness.txt'
                wp.write_text(''.join(''.join(str((adj[i] >> j) & 1) for j in range(N)) + '\n' for i in range(N)))
                status = 'WITNESS_PENDING_INDEPENDENT_REPLAY'
                break
            for ss in sorted(bad):
                cl = [lc.e(a, b) for a, b in itertools.combinations(ss, 2)]
                proj = tuple(v for v in cl if z.val(v) is None)
                if any(z.val(v) is True for v in cl):
                    continue
                if proj not in seen_cuts:
                    seen_cuts.add(proj)
                    cl_list = list(proj)
                    extra_cuts.append(cl_list)
                    sol.add_clause(cl_list)
                    i10_cuts += 1
                    added += 1
            assert added > 0
            if models % 20 == 0:
                print(json.dumps({
                    'task': task['id'], 'elapsed_s': round(time.monotonic() - t0, 2),
                    'models': models, 'i10_cuts': i10_cuts
                }), flush=True)

    proof_meta = {}
    if status == 'UNSAT_PENDING_PROOF':
        cnf_path = out_dir / 'leaf.cnf'
        drat_path = out_dir / 'leaf.drat'
        lrat_path = out_dir / 'leaf.lrat'
        with open(cnf_path, 'w') as f:
            f.write(f'p cnf {z.nv} {len(base_clauses) + len(extra_cuts)}\n')
            for cl in itertools.chain(base_clauses, extra_cuts):
                f.write(' '.join(map(str, cl)) + ' 0\n')
        def cap():
            resource.setrlimit(resource.RLIMIT_FSIZE, (2048 * 1024**2, 2048 * 1024**2))
        tp0 = time.monotonic()
        with open(out_dir / 'kissat.log', 'w') as log:
            p = subprocess.run(['kissat', f'--time={proof_seconds}', str(cnf_path), str(drat_path)],
                               stdout=log, stderr=subprocess.STDOUT, timeout=proof_seconds + 30, preexec_fn=cap)
        proof_meta['kissat_exit'] = p.returncode
        proof_meta['kissat_s'] = round(time.monotonic() - tp0, 3)
        if p.returncode == 20:
            tv0 = time.monotonic()
            with open(out_dir / 'drat-trim.log', 'w') as log:
                v = subprocess.run(['drat-trim', str(cnf_path), str(drat_path), '-L', str(lrat_path)],
                                   stdout=log, stderr=subprocess.STDOUT, timeout=proof_seconds)
            ok = (v.returncode == 0 and 's VERIFIED' in (out_dir / 'drat-trim.log').read_text(errors='replace'))
            proof_meta['drat_verified'] = ok
            proof_meta['drat_trim_s'] = round(time.monotonic() - tv0, 3)
            if ok:
                status = 'CERTIFIED_UNSAT'
                proof_meta['cnf_sha256'] = sha256_file(cnf_path)
                proof_meta['drat_sha256'] = sha256_file(drat_path)
                with open(drat_path, 'rb') as fi, gzip.open(out_dir / 'leaf.drat.gz', 'wb', compresslevel=1) as fo:
                    shutil.copyfileobj(fi, fo)
        drat_path.unlink(missing_ok=True)
        lrat_path.unlink(missing_ok=True)

    res = {
        'task': task['id'], 'status': status, 'elapsed_s': round(time.monotonic() - t0, 3),
        'models': models, 'i10_cuts': i10_cuts, 'base_vars': z.nv, 'base_clauses': len(base_clauses),
        'proof': proof_meta,
    }
    (out_dir / 'result.json').write_text(json.dumps(res, indent=2) + '\n')
    print(json.dumps(res, indent=2), flush=True)

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--tasks-json', required=True)
    ap.add_argument('--task', required=True)
    ap.add_argument('--out', default='out')
    ap.add_argument('--seconds', type=int, default=1200)
    ap.add_argument('--proof-seconds', type=int, default=300)
    a = ap.parse_args()
    task = json.loads(Path(a.tasks_json).read_text())[a.task]
    run_task(task, Path(a.out), a.seconds, a.proof_seconds)
