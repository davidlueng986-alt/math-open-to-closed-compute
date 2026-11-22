#!/usr/bin/env python3
"""Recheck a witness and merge exact coverage from the shard artifacts."""

from collections import Counter
from pathlib import Path
import json
import os
import sys

from run import DOMAINS, is_prime, verify_witness, write_json


def main():
    root, summary = map(Path, sys.argv[1:3])
    shards = int(os.environ["SHARDS"])
    primes = [p for p in range(2, max(d[2] for d in DOMAINS) + 1) if is_prime(p)]
    expected = {(n, low, cap): [p for p in primes[n - 1:] if low <= p <= cap]
                for n, low, cap, _ in DOMAINS}
    status = {key: {"done": set(), "counts": Counter()} for key in expected}
    witnesses = []
    metric_names = ("nodes", "suffix_queries", "signature_hits", "exact_tests", "square_hits")

    for shard in range(shards):
        file = root / f"shard-{shard}" / "result.json"
        if not file.exists():
            continue
        result = json.loads(file.read_text(encoding="utf-8"))
        if (result["shard"], result["shards"]) != (shard, shards):
            raise ValueError("incorrect shard identity")
        seen = set()
        for domain in result["domains"]:
            key = (domain["size"], domain["min_max_prime"], domain["max_prime"])
            if key in seen or (domain["shard"], domain["shards"]) != (shard, shards):
                raise ValueError("repeated domain or incorrect domain shard identity")
            seen.add(key)
            done, pending = domain["completed_max_primes"], domain["pending_max_primes"]
            if sorted(done + pending) != expected[key][shard::shards]:
                raise ValueError(f"incorrect coverage for {key} in shard {shard}")
            status[key]["done"].update(done)
            status[key]["counts"].update({k: domain[k] for k in metric_names})
            if "witness" in domain:
                witnesses.append(verify_witness(domain["witness"]))

    coverage = []
    for key, maxima in expected.items():
        n, low, cap = key
        remaining = sorted(set(maxima) - status[key]["done"])
        coverage.append({"size": n, "min_max_prime": low, "max_prime": cap,
                         "completed_max_prime_count": len(maxima) - len(remaining),
                         "pending_max_primes": remaining, **status[key]["counts"]})
    data = {"problem": "Erdős #307", "mathematical_status": "CLOSED YES" if witnesses else "OPEN",
            "described_domain_exhausted": all(not row["pending_max_primes"] for row in coverage),
            "coverage": coverage}
    if witnesses:
        write_json(summary / "witness.json", witnesses[0])
        print("CLOSED YES. Independent exact fraction verification passed.")
    else:
        print("OPEN. No witness in the completed domains.")
    write_json(summary / "erdos-307.json", data)
    for row in coverage:
        print(f"size {row['size']}: {row['completed_max_prime_count']} maximum-prime values complete, "
              f"{len(row['pending_max_primes'])} pending, {row.get('exact_tests', 0)} exact square tests")


if __name__ == "__main__":
    main()
