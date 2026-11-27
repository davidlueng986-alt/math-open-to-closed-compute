#!/usr/bin/env python3
"""Sharded Production Batch Runner for Tier-2 D78 NA-DAG Fixed-Core SAT Closure.

Designed for GitHub Actions (<= 10 shards, <= 5.5h wall-clock budget per shard) with:
  - mode=poc:  Controlled PoC on the 4 McKay (3,8; 27, 85) cores across T*=27 D78 branches
               (fast 1-pass verification mirroring V8 PoC Run 3's D9-C7 success).
  - mode=full: Deterministic round-robin sharding across all surviving Tier-2 D78
               (branch, core) work units supplied in cores_manifest.json, with atomic
               checkpointing, resume support, and hard 5.5h budget guard.

Also includes a streaming McKay r38_27.g6.gz extractor (`--extract-mckay-27`) that
verifies total count == 477,142 and filters cores by exact edge count e(T).
"""
import argparse
import gzip
import json
import os
import time
from pathlib import Path

from d78_core_cnf import decode_g6, proof_first_solve_core, verify_r38_core

MAX_SHARDS = 10
MAX_BUDGET_SECONDS = 19800  # 5.5 hours hard cap (leaves 30 min buffer inside 6h GHA limit)


def write_atomic_json(path: Path, obj: dict):
    tmp = path.with_suffix('.tmp')
    with open(tmp, 'w') as f:
        f.write(json.dumps(obj, indent=2) + '\n')
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)


def extract_mckay_r38_27(g6_gz_path: Path, target_edges=None, limit_per_eT=None):
    """Stream McKay's r38_27.g6.gz (477,142 graphs) and extract verified (3,8; 27, eT) cores."""
    target_set = set(target_edges) if target_edges is not None else None
    total = 0
    by_eT = {}
    opener = gzip.open if str(g6_gz_path).endswith('.gz') else open
    with opener(g6_gz_path, 'rt', encoding='ascii') as fp:
        for line in fp:
            s = line.strip().removeprefix('>>graph6<<')
            if not s:
                continue
            assert len(s) == 60 and ord(s[0]) - 63 == 27, f'Unexpected graph6 line: {s[:20]}'
            total += 1
            eT = sum((ord(ch) - 63).bit_count() for ch in s[1:])
            if target_set is not None and eT not in target_set:
                continue
            bucket = by_eT.setdefault(eT, [])
            if limit_per_eT is not None and len(bucket) >= limit_per_eT:
                continue
            adj = decode_g6(s, expected_n=27)
            edges_chk = verify_r38_core(adj, expected_n=27, check_alpha=True)
            assert edges_chk == eT
            bucket.append(s)
    assert total == 477142, f'Expected 477142 graphs in r38_27.g6.gz, got {total}'
    return {str(k): v for k, v in sorted(by_eT.items())}


def build_work_queue(manifest: dict, cores_by_nT_eT: dict, mode: str, branch_filter=None):
    """Build deterministic list of (branch, core_idx, g6, eT, t_range) work items."""
    branches = manifest['surviving_branches']
    if branch_filter:
        allowed = set(branch_filter)
        branches = [b for b in branches if b['branch_id'] in allowed]

    if mode == 'poc':
        branches = [b for b in branches if b['Tstar'] == 27]

    queue = []
    for br in branches:
        nT_key = str(br['Tstar'])
        eT_map = cores_by_nT_eT.get(nT_key, {})
        t_by_eT = br.get('a1_t_by_eT', {})
        allowed_eTs = br.get('a1_eT_values', [])
        if mode == 'poc':
            allowed_eTs = [e for e in allowed_eTs if e == 85]
        for eT in allowed_eTs:
            cores = eT_map.get(str(eT), [])
            t_rng = t_by_eT.get(str(eT)) or br.get('a1_t_range')
            for idx, g6 in enumerate(cores):
                work_id = f"{br['branch_id']}_e{eT}_c{idx:05d}"
                queue.append({
                    'work_id': work_id,
                    'branch_id': br['branch_id'],
                    'Tstar': br['Tstar'],
                    'du': br['du'],
                    'dv': br['dv'],
                    'c': br['c'],
                    'eT': eT,
                    'core_idx': idx,
                    'g6': g6,
                    't_range': t_rng,
                })
    return queue


def partition_shard(queue, shard_id: int, num_shards: int):
    """Deterministic round-robin sharding (0-indexed shard_id, 1 <= num_shards <= 10)."""
    assert 1 <= num_shards <= MAX_SHARDS, f'num_shards must be in 1..{MAX_SHARDS}'
    assert 0 <= shard_id < num_shards, f'shard_id {shard_id} out of range 0..{num_shards - 1}'
    return [item for idx, item in enumerate(queue) if idx % num_shards == shard_id]


def run_shard(
    manifest_path: Path,
    cores_path: Path,
    out_dir: Path,
    shard_id: int,
    num_shards: int,
    mode: str,
    budget_seconds: int,
    per_core_seconds: int,
    branch_filter=None,
    max_i7: int = 2000,
):
    assert 1 <= num_shards <= MAX_SHARDS
    assert 0 <= shard_id < num_shards
    budget_seconds = min(budget_seconds, MAX_BUDGET_SECONDS)

    manifest = json.loads(manifest_path.read_text())
    cores_by_nT_eT = json.loads(cores_path.read_text())
    full_queue = build_work_queue(manifest, cores_by_nT_eT, mode=mode, branch_filter=branch_filter)
    my_items = partition_shard(full_queue, shard_id, num_shards)

    out_dir.mkdir(parents=True, exist_ok=True)
    ckpt_path = out_dir / 'checkpoint.json'
    completed = {}
    if ckpt_path.exists():
        completed = json.loads(ckpt_path.read_text()).get('results', {})

    t0 = time.monotonic()
    counts = {'CERTIFIED_UNSAT': 0, 'OPEN_TIMEOUT': 0, 'VERIFIED_WITNESS_R310_40': 0, 'OTHER': 0, 'SKIPPED_BUDGET': 0}

    for item in my_items:
        wid = item['work_id']
        if wid in completed and completed[wid].get('status') in ('CERTIFIED_UNSAT', 'VERIFIED_WITNESS_R310_40'):
            st = completed[wid]['status']
            counts[st] = counts.get(st, 0) + 1
            continue
        rem = int(budget_seconds - (time.monotonic() - t0))
        if rem < 30:
            counts['SKIPPED_BUDGET'] += 1
            continue
        sec = min(per_core_seconds, rem - 15)
        res = proof_first_solve_core(
            g6=item['g6'],
            Tstar=item['Tstar'],
            du=item['du'],
            dv=item['dv'],
            out_dir=out_dir / wid,
            seconds=sec,
            t_range=item['t_range'],
            include_b2=False,
            include_i7=True,
            max_i7=max_i7,
            d78_strict=True,
        )
        completed[wid] = {
            'work_id': wid,
            'branch_id': item['branch_id'],
            'eT': item['eT'],
            'status': res['status'],
            'solve_seconds': res.get('solve_seconds'),
            'verify_seconds': res.get('verify_seconds'),
            'total_seconds': res.get('total_seconds'),
            'cuts': res.get('cuts', 0),
            'cnf_sha256': res.get('cnf_sha256'),
            'drat_sha256': res.get('drat_sha256'),
            'lrat_verified': res.get('lrat_verified'),
        }
        st = res['status']
        counts[st if st in counts else 'OTHER'] += 1
        write_atomic_json(ckpt_path, {
            'schema': 1,
            'mode': mode,
            'shard_id': shard_id,
            'num_shards': num_shards,
            'total_queue': len(full_queue),
            'shard_items': len(my_items),
            'counts': counts,
            'elapsed_seconds': round(time.monotonic() - t0, 2),
            'results': completed,
        })
        if st == 'VERIFIED_WITNESS_R310_40':
            break

    summary = {
        'schema': 1,
        'mode': mode,
        'shard_id': shard_id,
        'num_shards': num_shards,
        'total_queue': len(full_queue),
        'shard_items': len(my_items),
        'counts': counts,
        'elapsed_seconds': round(time.monotonic() - t0, 2),
    }
    write_atomic_json(out_dir / 'shard_summary.json', summary)
    print(json.dumps(summary, indent=2), flush=True)
    return summary


def main():
    ap = argparse.ArgumentParser(description='Tier-2 D78 NA-DAG Sharded Batch Runner')
    ap.add_argument('--extract-mckay-27', type=Path, help='Path to McKay r38_27.g6.gz to extract cores')
    ap.add_argument('--target-edges', type=str, default='85', help='Comma-separated e(T) values to extract')
    ap.add_argument('--limit-per-et', type=int, default=None)
    ap.add_argument('--cores-out', type=Path, default=Path('cores.json'))
    ap.add_argument('--manifest', type=Path)
    ap.add_argument('--cores-json', type=Path)
    ap.add_argument('--out-dir', type=Path, default=Path('out_shard'))
    ap.add_argument('--shard-id', type=int, default=0)
    ap.add_argument('--num-shards', type=int, default=4)
    ap.add_argument('--mode', choices=['poc', 'full'], default='poc')
    ap.add_argument('--budget-seconds', type=int, default=19800)
    ap.add_argument('--per-core-seconds', type=int, default=1500)
    ap.add_argument('--branches', type=str, default='', help='Optional comma-separated branch_id filter')
    ap.add_argument('--max-i7', type=int, default=2000)
    args = ap.parse_args()

    if args.extract_mckay_27:
        edges = [int(x) for x in args.target_edges.split(',') if x.strip()]
        by_eT = extract_mckay_r38_27(args.extract_mckay_27, target_edges=edges, limit_per_eT=args.limit_per_et)
        payload = {'27': by_eT}
        args.cores_out.parent.mkdir(parents=True, exist_ok=True)
        args.cores_out.write_text(json.dumps(payload, indent=2) + '\n')
        print(json.dumps({k: len(v) for k, v in by_eT.items()}), flush=True)
        return

    assert args.manifest and args.cores_json, 'Provide --manifest and --cores-json'
    br_filter = [x.strip() for x in args.branches.split(',') if x.strip()] or None
    run_shard(
        manifest_path=args.manifest,
        cores_path=args.cores_json,
        out_dir=args.out_dir,
        shard_id=args.shard_id,
        num_shards=args.num_shards,
        mode=args.mode,
        budget_seconds=args.budget_seconds,
        per_core_seconds=args.per_core_seconds,
        branch_filter=br_filter,
        max_i7=args.max_i7,
    )


if __name__ == '__main__':
    main()
