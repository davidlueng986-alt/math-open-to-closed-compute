#!/usr/bin/env python3
"""Merge shard results for Erdős #64, verify shard coverage, and re-verify any counterexample."""

import json
import os
import sys
from collections import defaultdict
from pathlib import Path

from run import verify_witness, write_json


def main():
    root, summary = map(Path, sys.argv[1:3])
    shards = int(float(os.environ["SHARDS"]))
    summary.mkdir(parents=True, exist_ok=True)

    lift_agg = {}
    sa_agg = defaultdict(lambda: {"evals": 0, "zeroC8": 0, "zeroC4_8_16": 0, "minC16_at_0C8": None})
    witnesses = []
    best_near_miss = None
    seen_shards = set()

    for shard in range(shards):
        result_file = root / f"shard-{shard}" / "result.json"
        if not result_file.exists():
            continue
        data = json.loads(result_file.read_text(encoding="utf-8"))
        if (data["shard"], data["shards"]) != (shard, shards):
            raise ValueError(f"mismatched shard identity in shard-{shard}")
        seen_shards.add(shard)

        for fam in data.get("lift_families", []):
            name = fam["name"]
            if name not in lift_agg:
                lift_agg[name] = {
                    "name": name,
                    "n": fam["n"],
                    "total_space": fam["total_space"],
                    "tested": 0,
                    "noC4": 0,
                    "noC4_8": 0,
                    "noC4_8_16": 0,
                    "noC4_32": 0,
                    "all_shards_completed": True,
                }
            entry = lift_agg[name]
            entry["tested"] += fam["tested"]
            entry["noC4"] += fam["noC4"]
            entry["noC4_8"] += fam["noC4_8"]
            entry["noC4_8_16"] += fam["noC4_8_16"]
            entry["noC4_32"] += fam["noC4_32"]
            if not fam["completed"]:
                entry["all_shards_completed"] = False

        for sr in data.get("sa_orders", []):
            n = sr["n"]
            entry = sa_agg[n]
            entry["evals"] += sr["evals"]
            entry["zeroC8"] += sr["zeroC8"]
            entry["zeroC4_8_16"] += sr["zeroC4_8_16"]
            mc = sr["minC16_at_0C8"]
            if mc is not None and mc >= 0:
                if entry["minC16_at_0C8"] is None or mc < entry["minC16_at_0C8"]:
                    entry["minC16_at_0C8"] = mc

        nm = data.get("best_near_miss")
        if nm is not None:
            if best_near_miss is None or nm["c16"] < best_near_miss["c16"]:
                best_near_miss = nm

        if "witness" in data:
            witnesses.append(verify_witness(data["witness"]))

    all_present = len(seen_shards) == shards
    lift_rows = []
    for entry in lift_agg.values():
        entry["exhausted"] = all_present and entry["all_shards_completed"] and (entry["tested"] == entry["total_space"])
        lift_rows.append(entry)

    sa_rows = [{"n": n, **sa_agg[n]} for n in sorted(sa_agg)]

    merged = {
        "problem": "Erdős #64 (Erdős–Gyárfás Conjecture)",
        "mathematical_status": "CLOSED NO" if witnesses else "OPEN",
        "shards_expected": shards,
        "shards_merged": len(seen_shards),
        "lift_families": lift_rows,
        "sa_orders": sa_rows,
    }
    if best_near_miss is not None:
        merged["best_near_miss"] = best_near_miss

    if witnesses:
        write_json(summary / "witness.json", witnesses[0])
        print("CLOSED NO. Independent exact cycle-length verification passed.")
    else:
        print("OPEN. No counterexample found in merged shards.")

    write_json(summary / "erdos-64-search.json", merged)
    for row in lift_rows:
        print(
            f"lift {row['name']} (n={row['n']}): tested={row['tested']}/{row['total_space']} "
            f"exhausted={row['exhausted']} noC4,8={row['noC4_8']} noC4,8,16={row['noC4_8_16']}"
        )
    for row in sa_rows:
        print(
            f"SA n={row['n']}: evals={row['evals']} zeroC8={row['zeroC8']} "
            f"minC16@0C8={row['minC16_at_0C8']} zeroC4,8,16={row['zeroC4_8_16']}"
        )


if __name__ == "__main__":
    main()
