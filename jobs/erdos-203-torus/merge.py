#!/usr/bin/env python3
"""Merge shard outputs from jobs/erdos-203-torus/ and audit verification checks.

usage: merge.py SHARDS_DIR SUMMARY_DIR
"""
import json
import os
import sys
from pathlib import Path


def main():
    shards_dir, summary_dir = Path(sys.argv[1]), Path(sys.argv[2])
    expected = int(float(os.environ.get("SHARDS", "0")))
    files = sorted(shards_dir.glob("shard-*/result.json"))
    if not files:
        sys.exit("no shard results found")

    records = []
    seen_shards = set()
    all_controls_ok = True
    all_verified = True

    for p in files:
        d = json.loads(p.read_text(encoding="utf-8"))
        if d.get("problem") != "ERDOS-203":
            sys.exit(f"unexpected problem tag in {p}: {d.get('problem')}")
        seen_shards.add(int(d["shard"]))
        if not d.get("positive_control_5040", False):
            all_controls_ok = False
        if not d.get("verified", False):
            all_verified = False
        records.append(d)

    if expected > 0 and seen_shards != set(range(expected)):
        missing = sorted(set(range(expected)) - seen_shards)
        sys.exit(f"missing shard results: {missing}")

    by_target = {}
    for d in records:
        key = f"K={d['K']},M0={d['M0']}"
        cur = by_target.get(key)
        if cur is None:
            by_target[key] = {
                "K": d["K"],
                "M0": d["M0"],
                "prime_limit": d["prime_limit"],
                "pool_size": d["pool_size"],
                "sum_inv_ep": d["sum_inv_ep"],
                "shards": 1,
                "total_restarts": d["restarts_completed"],
                "best_deficient_cells": d["deficient_cells"],
                "best_min_W": d["min_W"],
                "best_unkilled_cells": d["unkilled_cells"],
                "total_cells": d["total_cells"],
                "best_shard": d["shard"],
                "best_seed": d["best_seed"],
                "quotient_feasible": bool(d["quotient_feasible"]),
                "exact_cover_found": bool(d["exact_cover_found"]),
            }
        else:
            cur["shards"] += 1
            cur["total_restarts"] += d["restarts_completed"]
            if d["unkilled_cells"] < cur["best_unkilled_cells"]:
                cur["best_unkilled_cells"] = d["unkilled_cells"]
            better = (
                d["deficient_cells"] < cur["best_deficient_cells"]
                or (
                    d["deficient_cells"] == cur["best_deficient_cells"]
                    and d["min_W"] > cur["best_min_W"]
                )
            )
            if better:
                cur["best_deficient_cells"] = d["deficient_cells"]
                cur["best_min_W"] = d["min_W"]
                cur["best_shard"] = d["shard"]
                cur["best_seed"] = d["best_seed"]
            cur["quotient_feasible"] = cur["quotient_feasible"] or bool(d["quotient_feasible"])
            cur["exact_cover_found"] = cur["exact_cover_found"] or bool(d["exact_cover_found"])

    exact_covers = [k for k, v in by_target.items() if v["exact_cover_found"]]
    quotient_feasible = [k for k, v in by_target.items() if v["quotient_feasible"]]

    summary = {
        "problem": "ERDOS-203",
        "original_status": "OPEN",
        "shards_merged": len(records),
        "positive_controls_passed": all_controls_ok,
        "all_shards_verified": all_verified,
        "quotient_feasible_targets": quotient_feasible,
        "exact_cover_candidates": exact_covers,
        "targets": by_target,
        "note": (
            "quotient_feasible (deficient_cells=0, min_W>=1.0) certifies survival of the "
            "2D (Z/M0 Z)^2 Quotient Lemma necessary condition, NOT a complete cover of Z^2. "
            "Only exact_cover_found (unkilled_cells=0) followed by independent CRT verification "
            "closes Erdős #203 = YES."
        ),
    }

    summary_dir.mkdir(parents=True, exist_ok=True)
    (summary_dir / "erdos203_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2))
    if not (all_controls_ok and all_verified):
        sys.exit("verification or positive control failed in one or more shards")


if __name__ == "__main__":
    main()
