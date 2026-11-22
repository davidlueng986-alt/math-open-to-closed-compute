#!/usr/bin/env python3
"""Check that each partition was collected and summarize the level-61 exclusion."""

from collections import Counter
import json
import os
from pathlib import Path
import sys

from run import check_bounds, primes_through


def main():
    root, summary = map(Path, sys.argv[1:3])
    shards = int(os.environ["SHARDS"])
    check_bounds()
    same_counts = Counter()
    opposite_counts = Counter()
    candidates = []
    missing = []
    same_prefixes = set()
    large_q_totals = set()
    maxima = primes_through(1190)[58:]
    for shard in range(shards):
        file = root / f"shard-{shard}" / "result.json"
        if not file.is_file():
            missing.append(shard)
            continue
        result = json.loads(file.read_text(encoding="utf-8"))
        if (result["shard"], result["shards"]) != (shard, shards):
            raise ValueError(f"incorrect shard identity for {shard}")
        same = result["same"]
        if sorted(row["third"] for row in same) != [7, 11][shard::shards]:
            raise ValueError(f"incorrect same-side prefix assignment for {shard}")
        for row in same:
            same_prefixes.add(row["third"])
            same_counts.update({key: val for key, val in row.items() if key != "third"})
        opposite = result["opposite"]
        if (opposite["small_maxima"] != maxima[shard::shards] or
            opposite["prefixes_processed"] != len(range(shard, opposite["prefixes"], shards))):
            raise ValueError(f"incorrect opposite-side coverage in shard {shard}")
        large_q_totals.add((opposite["large_q_supports"], opposite["prefixes"]))
        opposite_counts.update({key: val for key, val in opposite.items()
                                if key not in ("large_q_supports", "prefixes", "seconds", "small_maxima")})
        candidates.extend(result["candidate_details"])

    if len(large_q_totals) != 1:
        raise ValueError("shards disagree on the large-q core and prefix lists")
    large_q_supports, large_q_prefixes = large_q_totals.pop()
    candidate_count = same_counts["roots"] + opposite_counts["opposite_candidates"]
    if candidate_count != len(candidates):
        raise ValueError("candidate count does not match the exact log")
    excluded = not missing and not candidate_count and same_prefixes == {7, 11}

    data = {
        "problem": "Erdős #307",
        "mathematical_status": "OPEN",
        "support_size": 61,
        "side_sizes_even_first": [49, 12],
        "two_tail_case_excluded": excluded,
        "missing_shards": missing,
        "same_side": same_counts,
        "opposite_sides": {**opposite_counts, "large_q_supports": large_q_supports,
                           "large_q_prefixes": large_q_prefixes},
        "candidate_details": candidates,
    }
    (summary / "dual61.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data))


if __name__ == "__main__":
    main()
