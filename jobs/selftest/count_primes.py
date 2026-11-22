#!/usr/bin/env python3
"""Self-test shard: count primes in this shard's slice of [2, N] with a segmented sieve.

usage: count_primes.py SHARD SHARDS OUTDIR     (N defaults to 10**7; override with SELFTEST_N)
"""
import json
import math
import os
import sys
from pathlib import Path


def base_primes(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(range(p * p, limit + 1, p)))
    return [i for i in range(limit + 1) if sieve[i]]


def count_in(lo, hi, primes):
    """Number of primes in [lo, hi)."""
    if hi <= lo:
        return 0
    seg = bytearray([1]) * (hi - lo)
    for p in primes:
        if p * p >= hi:
            break
        start = max(p * p, (lo + p - 1) // p * p)
        seg[start - lo::p] = bytearray(len(range(start, hi, p)))
    return sum(seg)


def main():
    shard, shards, outdir = int(sys.argv[1]), int(sys.argv[2]), Path(sys.argv[3])
    n_max = int(os.environ.get("SELFTEST_N", 10**7))
    span = n_max - 1  # numbers 2..n_max
    lo = 2 + span * shard // shards
    hi = 2 + span * (shard + 1) // shards
    count = count_in(lo, hi, base_primes(math.isqrt(n_max) + 1))
    outdir.mkdir(parents=True, exist_ok=True)
    result = {"shard": shard, "shards": shards, "n_max": n_max, "lo": lo, "hi": hi, "count": count}
    (outdir / "result.json").write_text(json.dumps(result) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
