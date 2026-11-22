#!/usr/bin/env python3
"""Check single-tail shard coverage and compile an exclusion report."""

from collections import Counter
import json
import os
from pathlib import Path
import sys

from run import CORE_SIZE, SHAPES, parameters


def main():
    root, out = map(Path, sys.argv[1:3])
    shards = int(os.environ["SHARDS"])
    primes, height = parameters()
    expected = primes[CORE_SIZE - 1:]
    counts = Counter()
    candidates, missing = [], []
    for shard in range(shards):
        path = root / f"shard-{shard}" / "result.json"
        if not path.is_file():
            missing.append(shard)
            continue
        data = json.loads(path.read_text(encoding="utf-8"))
        if (data["shard"], data["shards"], data["height"], data["max_primes"]) != (
            shard, shards, height, expected[shard::shards]
        ):
            raise ValueError(f"incorrect coverage for shard {shard}")
        fields = ("supports", "reciprocity_kills", "mass_kills", "uncovered", "reconstructed",
                  "derivative_matches", "composite_tails", "candidates")
        counts.update({k: data[k] for k in fields})
        candidates.extend(data["candidate_details"])

    excluded = not missing and counts["uncovered"] == counts["candidates"] == 0
    splits = [(n + 1, CORE_SIZE - n) if p == 2 else (CORE_SIZE - n, n + 1) for n, p in SHAPES]
    result = {"problem": "Erdős #307", "mathematical_status": "OPEN", "side_sizes_even_first": splits,
              "single_tail_sectors_excluded": excluded, "height": height, "missing_shards": missing,
              "counts": counts, "candidate_details": candidates}
    (out / "tail61.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
