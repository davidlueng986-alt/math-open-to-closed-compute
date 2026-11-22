#!/usr/bin/env python3
"""Check that the shards tile [2, N] exactly and that the prime counts add up to pi(N).

usage: merge.py SHARDS_DIR SUMMARY_DIR
"""
import json
import sys
from pathlib import Path

KNOWN_PI = {10**6: 78498, 10**7: 664579, 10**8: 5761455}


def main():
    shards_dir, summary_dir = Path(sys.argv[1]), Path(sys.argv[2])
    parts = sorted((json.loads(p.read_text()) for p in shards_dir.glob("shard-*/result.json")),
                   key=lambda r: r["lo"])
    if not parts:
        sys.exit("no shard results")
    n_max = parts[0]["n_max"]
    tiled = parts[0]["lo"] == 2 and parts[-1]["hi"] == n_max + 1 and all(
        a["hi"] == b["lo"] for a, b in zip(parts, parts[1:]))
    total = sum(p["count"] for p in parts)
    expected = KNOWN_PI.get(n_max)
    ok = tiled and (expected is None or total == expected)
    check = {"n_max": n_max, "shards": len(parts), "tiled_exactly": tiled,
             "prime_count": total, "expected": expected, "ok": ok}
    (summary_dir / "selftest_check.json").write_text(json.dumps(check, indent=2) + "\n")
    print(json.dumps(check))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
