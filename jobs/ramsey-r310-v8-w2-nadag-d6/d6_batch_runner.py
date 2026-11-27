#!/usr/bin/env python3
r"""Sharded Production Batch Runner for Unified NA-DAG Tier-1 D6 Closure.

Supports:
  - <= 10 shards (--num-shards 1..10, --shard-id 0..num-shards-1)
  - <= 5.5h per-shard wall-clock budget (--budget-seconds <= 19800)
  - mode=poc: fast 20m benchmark on curated McKay (3, 8; 27, 85) cores across r=5 branches
  - mode=full: deterministic sharded production sweep over all selected (branch, core) tasks
  - Atomic checkpointing (checkpoint.json) with zero duplicate/omitted items across shards.
"""
import argparse
import json
import os
import time
from pathlib import Path

import d6_core_cnf as core_cnf
import d6_nadag_pruner as pruner

MAX_SHARDS = 10
MAX_BUDGET_SECONDS = 19800  # 5.5 hours


def write_atomic_json(path: Path, obj: dict) -> None:
    tmp = path.with_suffix(".tmp")
    with open(tmp, "w") as f:
        f.write(json.dumps(obj, indent=2) + "\n")
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)


def build_work_queue(plan_obj: dict, cores_by_nt: dict, branch_filter=None, max_per_branch=None):
    """Build deterministic ordered list of (branch_id, r, q, eT, core_idx, g6, t_bounds) items."""
    items = []
    for b in plan_obj["branches"]:
        if b["status"] == "CLOSED_PURE_INTEGER":
            continue
        if branch_filter and b["id"] not in branch_filter:
            continue
        nt = b["nt"]
        r, q = b["r"], b["q"]
        eT_to_t = b.get("eT_to_t", {})
        cores = cores_by_nt.get(nt, [])
        added = 0
        for idx, (eT, g6) in enumerate(cores):
            ts = eT_to_t.get(str(eT))
            if not ts:
                continue
            items.append(
                dict(
                    item_id=f"{b['id']}-E{eT}-C{idx:06d}",
                    branch_id=b["id"],
                    r=r,
                    q=q,
                    nt=nt,
                    eT=eT,
                    core_idx=idx,
                    g6=g6,
                    t_bounds=[min(ts), max(ts)],
                )
            )
            added += 1
            if max_per_branch is not None and added >= max_per_branch:
                break
    return items


def assign_shard(items: list, shard_id: int, num_shards: int) -> list:
    assert 1 <= num_shards <= MAX_SHARDS, f"num_shards must be in 1..{MAX_SHARDS}"
    assert 0 <= shard_id < num_shards, f"shard_id must be in 0..{num_shards - 1}"
    return [item for idx, item in enumerate(items) if idx % num_shards == shard_id]


def run_shard(
    plan_path: Path,
    g6_path: Path,
    out_dir: Path,
    mode: str,
    shard_id: int,
    num_shards: int,
    budget_seconds: int,
    per_core_seconds: int,
    nt: int = 27,
    e_lo: int = 85,
    e_hi: int = 85,
    branch_filter=None,
    dry_run: bool = False,
):
    assert 1 <= num_shards <= MAX_SHARDS, f"num_shards={num_shards} exceeds MAX_SHARDS={MAX_SHARDS}"
    assert 0 <= shard_id < num_shards
    assert budget_seconds <= MAX_BUDGET_SECONDS, (
        f"budget_seconds={budget_seconds} exceeds 5.5h cap ({MAX_BUDGET_SECONDS}s)"
    )

    out_dir.mkdir(parents=True, exist_ok=True)
    plan_obj = json.loads(plan_path.read_text())

    if mode == "poc":
        # PoC benchmark: all 4 McKay (3,8; 27, 85) cores across r=5 branches, 20m cap
        e_lo, e_hi = 85, 85
        budget_seconds = min(budget_seconds, 1200)
        per_core_seconds = min(per_core_seconds, 600)
        max_per_branch = 4
    else:
        max_per_branch = None

    total_scanned, selected_cores = core_cnf.extract_cores_from_g6(g6_path, nt, e_lo, e_hi)
    all_items = build_work_queue(
        plan_obj,
        cores_by_nt={nt: selected_cores},
        branch_filter=branch_filter,
        max_per_branch=max_per_branch,
    )
    shard_items = assign_shard(all_items, shard_id, num_shards)

    ckpt_path = out_dir / "checkpoint.json"
    results = []
    if ckpt_path.exists():
        prev = json.loads(ckpt_path.read_text())
        results = prev.get("results", [])
    done_ids = {r["item_id"] for r in results if r.get("status") != "OPEN_TIMEOUT"}

    t0 = time.monotonic()
    counts = dict(
        certified_unsat=0,
        certified_unsat_pruner=0,
        verified_witness=0,
        open_timeout=0,
        failed=0,
    )

    for item in shard_items:
        if item["item_id"] in done_ids:
            continue
        rem = budget_seconds - (time.monotonic() - t0)
        if rem < 15:
            break
        if dry_run:
            res = dict(item_id=item["item_id"], branch_id=item["branch_id"], status="DRY_RUN")
        else:
            step_sec = min(per_core_seconds, int(rem - 5))
            res = core_cnf.proof_first_solve_core(
                g6=item["g6"],
                r=item["r"],
                q=item["q"],
                out_dir=out_dir / item["item_id"],
                seconds=step_sec,
                t_bounds=tuple(item["t_bounds"]),
                include_i7=True,
                max_i7=2000,
            )
            res["item_id"] = item["item_id"]
            res["eT"] = item["eT"]
        results.append(res)
        st = res.get("status", "")
        if st == "CERTIFIED_UNSAT":
            counts["certified_unsat"] += 1
        elif st == "CERTIFIED_UNSAT_PRUNER":
            counts["certified_unsat_pruner"] += 1
        elif st == "VERIFIED_WITNESS":
            counts["verified_witness"] += 1
        elif st == "OPEN_TIMEOUT":
            counts["open_timeout"] += 1
        elif st != "DRY_RUN":
            counts["failed"] += 1

        write_atomic_json(
            ckpt_path,
            dict(
                schema=1,
                mode=mode,
                shard_id=shard_id,
                num_shards=num_shards,
                total_scanned_g6=total_scanned,
                total_work_items=len(all_items),
                shard_work_items=len(shard_items),
                completed_items=len(results),
                counts=counts,
                elapsed_seconds=round(time.monotonic() - t0, 3),
                results=results,
            ),
        )
        if st == "VERIFIED_WITNESS":
            break

    summary = dict(
        schema=1,
        mode=mode,
        shard_id=shard_id,
        num_shards=num_shards,
        total_scanned_g6=total_scanned,
        total_work_items=len(all_items),
        shard_work_items=len(shard_items),
        completed_items=len(results),
        counts=counts,
        elapsed_seconds=round(time.monotonic() - t0, 3),
    )
    write_atomic_json(out_dir / "shard_summary.json", summary)
    print(json.dumps(summary, indent=2), flush=True)
    return summary


def main():
    ap = argparse.ArgumentParser(description="Tier-1 D6 NA-DAG Sharded Batch Runner")
    ap.add_argument("--plan", type=Path, required=True, help="Path to d6_nadag_plan.json")
    ap.add_argument("--g6-file", type=Path, required=True, help="Path to r38_<nT>.g6(.gz)")
    ap.add_argument("--out-dir", type=Path, required=True)
    ap.add_argument("--mode", choices=["poc", "full"], default="poc")
    ap.add_argument("--shard-id", type=int, default=0)
    ap.add_argument("--num-shards", type=int, default=4)
    ap.add_argument("--budget-seconds", type=int, default=1200)
    ap.add_argument("--per-core-seconds", type=int, default=900)
    ap.add_argument("--nt", type=int, default=27, choices=[25, 26, 27])
    ap.add_argument("--e-lo", type=int, default=85)
    ap.add_argument("--e-hi", type=int, default=85)
    ap.add_argument("--branches", type=str, default="", help="Comma-separated branch IDs (optional)")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    bfilter = [x.strip() for x in a.branches.split(",") if x.strip()] or None
    run_shard(
        plan_path=a.plan,
        g6_path=a.g6_file,
        out_dir=a.out_dir,
        mode=a.mode,
        shard_id=a.shard_id,
        num_shards=a.num_shards,
        budget_seconds=a.budget_seconds,
        per_core_seconds=a.per_core_seconds,
        nt=a.nt,
        e_lo=a.e_lo,
        e_hi=a.e_hi,
        branch_filter=bfilter,
        dry_run=a.dry_run,
    )


if __name__ == "__main__":
    main()
