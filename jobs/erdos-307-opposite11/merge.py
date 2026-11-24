#!/usr/bin/env python3
"""Verify coverage and report the sum of exact search results."""
from collections import Counter
import json
from pathlib import Path
import sys
from run import check_bounds, number_of_prefixes


def main():
    # collect.py passes the directory of shard outputs and the summary directory.
    shards_dir, output = map(Path, sys.argv[1:3])
    check_bounds()
    summaries = []
    for p in sorted(shards_dir.glob("shard-*/result.json")):
        summaries.append(json.loads(p.read_text()))
    if not summaries:
        raise ValueError("no shard results")
    n = summaries[0]["shards"]
    tasks = number_of_prefixes()
    if sorted(r["shard"] for r in summaries) != list(range(n)):
        raise ValueError("missing or duplicate shard")
    for r in summaries:
        if (r["shards"] != n or r["tasks"] != tasks or r["complete"] != 1
                or r["done"] != len(range(r["shard"], tasks, n))):
            raise ValueError("invalid per-shard coverage")
    counts = Counter()
    for record in summaries:
        counts.update({k: v for k, v in record.items()
                       if k not in {"tasks", "shard", "shards", "large_supports",
                                    "complete", "seconds", "candidate_details"}})
    if len({r["large_supports"] for r in summaries}) != 1:
        raise ValueError("different bounded union catalogs")
    report = {"problem": "ERDOS-307", "level": 61, "split": [11, 50],
              "first_side_even": True, "placement": "opposite",
              "opposite_placement_excluded": not counts["candidates"],
              "original_status": "OPEN", "prefixes": tasks, "counts": dict(counts),
              "large_tail_supports": summaries[0]["large_supports"],
              "longest_shard_seconds": max(r["seconds"] for r in summaries),
              "candidate_details": [p for r in summaries for p in r["candidate_details"]]}
    output.mkdir(parents=True, exist_ok=True)
    (output / "opposite11.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
