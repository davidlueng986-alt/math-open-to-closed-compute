#!/usr/bin/env python3
"""Sharded batch runner for D9-C5, D9-C4, and D9-C3 surviving canonical skeleton orbits.

Designed for GitHub Actions (<= 10 shards, <= 5.5h wall-clock budget per shard):
  - Loads surviving orbits from d9c345_farkas_certificates.json or orbits_manifest.json (never re-runs Farkas-pruned orbits).
  - Orders orbits by (c descending, e_xy descending, id) so tightest high-e_xy skeletons solve first.
  - Interleaves orbits round-robin across `num_shards` for balanced load.
  - Runs single-pass Proof-First Kissat + drat-trim + lrat-check per orbit within budget.
  - Halts immediately and persists witness if any verified 40-vertex R(3,10) witness is found.
"""
import argparse
import json
import os
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import d9c345_compact_cnf as solver


def load_surviving_orbits(cert_bundle_path: Path, case_selector: str):
    bundle = json.loads(cert_bundle_path.read_text())
    if case_selector == 'ALL':
        keys = [k for k in ('C5', 'C4', 'C3') if k in bundle['cases']]
    else:
        assert case_selector in bundle['cases'], f"Case {case_selector} not found in {cert_bundle_path}"
        keys = [case_selector]
    orbits = []
    for k in keys:
        orbits.extend(bundle['cases'][k]['surviving_orbits'])
    # Tightest orbits first (higher c, higher e_xy)
    orbits.sort(key=lambda o: (-o['c'], -o['e_xy'], o['id']))
    return orbits


def assign_shard(orbits, shard_index: int, num_shards: int):
    assert 1 <= num_shards <= 10, f"num_shards must be in [1, 10], got {num_shards}"
    assert 0 <= shard_index < num_shards, f"shard_index {shard_index} out of range [0, {num_shards})"
    return [o for idx, o in enumerate(orbits) if idx % num_shards == shard_index]


def write_atomic_json(path: Path, obj: dict):
    tmp = path.with_suffix('.tmp')
    with open(tmp, 'w') as f:
        f.write(json.dumps(obj, indent=2) + '\n')
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)


def run_shard(cert_bundle_path: Path, case_selector: str, shard_index: int, num_shards: int,
              out_dir: Path, budget_seconds: int = 19200, per_orbit_seconds: int = 600,
              dry_run: bool = False):
    assert budget_seconds <= 19800, f"budget_seconds {budget_seconds} exceeds 5.5h (19800s) cap"
    out_dir.mkdir(parents=True, exist_ok=True)
    all_orbits = load_surviving_orbits(cert_bundle_path, case_selector)
    my_orbits = assign_shard(all_orbits, shard_index, num_shards)

    t0 = time.monotonic()
    results = []
    certified = 0
    timeouts = 0
    witness_found = False

    if dry_run:
        summary = {
            'case': case_selector,
            'shard_index': shard_index,
            'num_shards': num_shards,
            'total_surviving_orbits': len(all_orbits),
            'shard_orbit_count': len(my_orbits),
            'dry_run': True,
            'first_3_orbits': [o['id'] for o in my_orbits[:3]],
        }
        write_atomic_json(out_dir / 'shard_summary.json', summary)
        print(json.dumps(summary, indent=2), flush=True)
        return summary

    for orb in my_orbits:
        elapsed = time.monotonic() - t0
        rem = int(budget_seconds - elapsed)
        if rem < 15:
            break
        sec = min(per_orbit_seconds, rem)
        orb_dir = out_dir / orb['id']
        rep = solver.proof_first_solve(
            orb['c'], orb['rows'], orb_dir, seconds=sec, adj_T=None, orbit_id=orb['id']
        )
        results.append({
            'id': orb['id'],
            'c': orb['c'],
            'e_xy': orb['e_xy'],
            'status': rep['status'],
            'total_seconds': rep.get('total_seconds', 0),
            'cuts': rep.get('cuts', 0),
        })
        if rep['status'] == 'CERTIFIED_UNSAT':
            certified += 1
        elif rep['status'] == 'VERIFIED_WITNESS':
            witness_found = True
            break
        else:
            timeouts += 1

    status = 'VERIFIED_WITNESS' if witness_found else (
        'SHARD_COMPLETE_ALL_CERTIFIED' if certified == len(my_orbits) else 'PARTIAL_BUDGET_REACHED'
    )
    summary = {
        'case': case_selector,
        'shard_index': shard_index,
        'num_shards': num_shards,
        'total_surviving_orbits': len(all_orbits),
        'shard_orbit_count': len(my_orbits),
        'attempted': len(results),
        'certified_unsat': certified,
        'timeouts_or_open': timeouts,
        'witness_found': witness_found,
        'status': status,
        'elapsed_seconds': round(time.monotonic() - t0, 3),
        'results': results,
    }
    write_atomic_json(out_dir / 'shard_summary.json', summary)
    print(json.dumps(summary, indent=2), flush=True)
    return summary


def main():
    ap = argparse.ArgumentParser(description='Sharded D9-C3/C4/C5 Proof-First batch runner')
    ap.add_argument('--certs', type=Path, required=True, help='Path to orbits_manifest.json or d9c345_farkas_certificates.json')
    ap.add_argument('--case', required=True, choices=['C5', 'C4', 'C3', 'ALL'])
    ap.add_argument('--shard-index', type=int, required=True)
    ap.add_argument('--num-shards', type=int, default=10)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--budget-seconds', type=int, default=19200)
    ap.add_argument('--per-orbit-seconds', type=int, default=600)
    ap.add_argument('--dry-run', action='store_true')
    args = ap.parse_args()
    run_shard(
        args.certs, args.case, args.shard_index, args.num_shards,
        args.out, args.budget_seconds, args.per_orbit_seconds, args.dry_run
    )


if __name__ == '__main__':
    main()
