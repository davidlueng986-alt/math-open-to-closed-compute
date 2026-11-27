#!/usr/bin/env python3
"""Proof-First Kissat/DRAT and SMS (`smsg`) Container Runner for Lean-CNF V8."""
import argparse, json, resource, subprocess, time
from pathlib import Path
from lean_cnf_sms import build_lean_cnf, N

def run_kissat_drat(cnf_path: Path, out_dir: Path, seconds: int):
    drat_path = out_dir / 'leaf.drat'
    res = {'solver': 'kissat', 'certificate': 'NOT_VERIFIED'}
    t0 = time.monotonic()
    def cap(): resource.setrlimit(resource.RLIMIT_FSIZE, (1024 * 1024**2, 1024 * 1024**2))
    try:
        with open(out_dir / 'kissat.log', 'w') as log:
            p = subprocess.run(['kissat', str(cnf_path), str(drat_path)], stdout=log, stderr=subprocess.STDOUT, timeout=seconds, preexec_fn=cap)
        res['kissat_exit'] = p.returncode; res['kissat_s'] = round(time.monotonic() - t0, 3)
        if p.returncode == 20:
            t1 = time.monotonic()
            with open(out_dir / 'drat-trim.log', 'w') as log:
                v = subprocess.run(['drat-trim', str(cnf_path), str(drat_path)], stdout=log, stderr=subprocess.STDOUT, timeout=seconds)
            res['drat_trim_s'] = round(time.monotonic() - t1, 3)
            if v.returncode == 0 and 's VERIFIED' in (out_dir / 'drat-trim.log').read_text(errors='replace'):
                res['certificate'] = 'VERIFIED_UNSAT'
    except subprocess.TimeoutExpired:
        res['status'] = 'TIMEOUT'
    finally:
        drat_path.unlink(missing_ok=True)
    return res

def run_smsg_probe(cnf_path: Path, part_sizes, out_dir: Path, seconds: int):
    cmd = ['smsg', '-v', str(N), '--cnf', str(cnf_path), '--initial-partition'] + [str(x) for x in part_sizes]
    t0 = time.monotonic()
    try:
        with open(out_dir / 'smsg.log', 'w') as log:
            p = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, timeout=seconds)
        return {'solver': 'smsg', 'exit': p.returncode, 'wall_s': round(time.monotonic() - t0, 3), 'cmd': cmd}
    except subprocess.TimeoutExpired:
        return {'solver': 'smsg', 'status': 'TIMEOUT', 'wall_s': round(time.monotonic() - t0, 3), 'cmd': cmd}

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--tasks-json', required=True); p.add_argument('--task', required=True)
    p.add_argument('--mode', choices=['proof-first-kissat', 'sms-probe'], default='proof-first-kissat')
    p.add_argument('--out', default='out'); p.add_argument('--seconds', type=int, default=600)
    a = p.parse_args()
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    task = json.loads(Path(a.tasks_json).read_text())[a.task]
    sym_mode = 'static_lex' if a.mode == 'proof-first-kissat' else 'sms'
    z, meta = build_lean_cnf(task, sym_mode=sym_mode)
    cnf_path = out / f'{a.task}.{sym_mode}.cnf'; z.write_dimacs(cnf_path); meta['cnf_path'] = str(cnf_path)
    if meta.get('unsat_by_prefilter'): meta['result'] = {'status': 'UNSAT_BY_V8_KONIG_PREFILTER'}
    elif a.mode == 'proof-first-kissat': meta['result'] = run_kissat_drat(cnf_path, out, a.seconds)
    else: meta['result'] = run_smsg_probe(cnf_path, meta['sms_partition_sizes'], out, a.seconds)
    (out / 'summary.json').write_text(json.dumps(meta, indent=2) + '\n')
    print(json.dumps(meta, indent=2), flush=True)
