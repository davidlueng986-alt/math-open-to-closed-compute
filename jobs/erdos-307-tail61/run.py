#!/usr/bin/env python3
"""Enumerate single-tail completions at the first open support size."""

from fractions import Fraction
from math import isqrt, prod
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile


CUTOFF = 2381
CORE_SIZE = 60
DEFICIT = Fraction(1, 10**30)
SHAPES = ((10, 2), (12, 2), (11, 3), (13, 3))
DIRECTORY = Path(__file__).resolve().parent


def primes_through(cap):
    return [p for p in range(2, cap + 1) if all(p % d for d in range(2, isqrt(p) + 1))]


def parameters():
    primes = primes_through(CUTOFF)
    masses = [Fraction()]
    for p in primes[:CORE_SIZE + 1]:
        masses.append(masses[-1] + Fraction(1, p))

    side_lower, side_upper = Fraction(907, 1000), Fraction(1103, 1000)
    assert masses[61] < min(s + 1 / s for s in (side_lower, side_upper))
    assert masses[61] - Fraction(1, 103) < 2 - DEFICIT
    assert side_lower - DEFICIT > Fraction(906, 1000)
    rank_caps = []
    for j in range(1, CORE_SIZE + 1):
        deficit = 2 - DEFICIT - masses[j - 1]
        rank_caps.append(min(CUTOFF, (CORE_SIZE + 1 - j) // deficit) if deficit > 0 else CUTOFF)

    bounds = []
    for size, smallest_allowed in SHAPES:
        other_side = prod(primes[:CORE_SIZE - size])
        # The large prime is forced onto the small side, which then has product at least this large.
        assert other_side > side_upper * CUTOFF**(size + 1) / DEFICIT
        lower = [Fraction(1, cap) for cap in rank_caps[-size:]]
        eligible = primes if smallest_allowed == 2 else primes[1:]
        upper = [Fraction(1, p) for p in eligible[:size]]
        if smallest_allowed == 2:
            lower[0] = Fraction(1, 2)
        remaining = max(Fraction(), Fraction(906, 1000) - sum(lower))
        for i, upper_bound in enumerate(upper):
            assert lower[i] <= upper_bound
            amount = min(remaining, upper_bound - lower[i])
            lower[i] += amount
            remaining -= amount
        assert remaining == 0
        bounds.append(int(1 / prod(lower)))

    return primes, max(bounds)


def main():
    shard, shards = map(int, sys.argv[1:3])
    out = Path(sys.argv[3])
    if not 0 <= shard < shards <= 256:
        raise ValueError("invalid shard assignment")
    out.mkdir(parents=True, exist_ok=True)
    primes, H = parameters()
    env = os.environ.copy()
    env.setdefault("OMP_NUM_THREADS", str(min(4, os.cpu_count() or 1)))

    with tempfile.TemporaryDirectory(prefix="erdos-307-tail61-") as temp:
        binary = Path(temp) / "search"
        subprocess.run(["g++", "-std=c++20", "-O3", "-fopenmp", "-Wall", "-Wextra", "-Werror",
                        str(DIRECTORY / "search.cpp"), "-lgmpxx", "-lgmp", "-o", str(binary)],
                       check=True, timeout=120)
        result = subprocess.run([str(binary), *map(str, (H, CUTOFF, shard, shards))],
                                env=env, capture_output=True, text=True, check=True, timeout=960)
    counts = json.loads(result.stdout)
    summary = {**counts, "shard": shard, "shards": shards, "height": H,
               "max_primes": primes[CORE_SIZE - 1:][shard::shards],
               "candidate_details": result.stderr.splitlines()}
    (out / "result.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
