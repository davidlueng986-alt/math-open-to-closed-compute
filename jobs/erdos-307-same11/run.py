#!/usr/bin/env python3
"""Check the analytical bounds and run one shard of the (11,50) same-side placement."""

import json
import os
from fractions import Fraction
from math import isqrt, prod
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
SCALE = 1 << 62


def primes_up_to(limit):
    return [p for p in range(2, limit + 1) if all(p % i for i in range(2, isqrt(p) + 1))]


def check_bounds():
    primes = primes_up_to(2381)
    total = [Fraction(0)]
    for p in primes[:62]:
        total.append(total[-1] + Fraction(1, p))
    tiny = Fraction(1, 10**20)
    tau = Fraction(1, 2382) + tiny
    assert total[61] < 3
    assert total[58] + Fraction(3, 2382) < 2
    assert 3 * max(2381**11, 10**20 * 2381**10, 10**40 * 2381**9) < prod(primes[:50])
    for cap, mandatory, t in [(1190, 157, tau), (794, 167, Fraction(1, 20_000_000) + tiny)]:
        assert total[58] + Fraction(1, cap + 1) + t < 2
        assert total[60] - Fraction(1, mandatory) + t < 2
    for x in [Fraction(948, 1000), Fraction(1055, 1000)]:
        assert total[59] + tau < x + 1 / x
    assert Fraction(947, 1000) * prod(primes[:49]) > 1190**10
    assert tiny * SCALE < 1
    assert Fraction((SCALE + 2381) // 2382 + 1, SCALE) > tau

    # The ith prime of a size-59 union is at most (60-i)/(2-T_(i-1)-tau).
    ranks = [min(1190, (59 - i) // (2 - total[i] - tau)) for i in range(59)]
    assert ranks == sorted(ranks)
    mandatory = [p for p in primes if p <= 157]
    assert len(mandatory) == 37
    optional = [p for p in primes if p > 157]
    for c in range(11):
        k_min = Fraction(947, 1000) * prod(mandatory) * prod(optional[:10-c])
        assert k_min > 20_000_000 * prod(ranks[-(12+c):])

    # A product of nine primes has nine ordered reciprocal coordinates.
    # At the smallest permitted sum, filling the largest coordinates first
    # minimizes their product by log-concavity and majorization.
    lower = [Fraction(1, r) for r in ranks[-9:]]
    upper = [Fraction(1, p) for p in primes[:9]]
    lower[0] = Fraction(1, 2)
    extra = Fraction(948, 1000) - tau - sum(lower)
    for i, cap in enumerate(upper):
        add = min(extra, cap - lower[i])
        assert add >= 0
        lower[i] += add
        extra -= add
    assert extra == 0 and prod(lower) > Fraction(1, 10**18)


def number_of_prefixes():
    size = 9
    # Independent enumeration of the five smallest primes of the small core.
    weights = [(SCALE + p - 1)//p for p in primes_up_to(1190)]
    lo = SCALE * 948 // 1000 - ((SCALE + 2381)//2382 + 1)

    def visit(partial, first, depth):
        left = size - depth
        if depth == 5:
            return 1
        count = 0
        for j in range(first, len(weights) - left + 1):
            if partial + sum(weights[j:j+left]) < lo:
                break
            count += visit(partial + weights[j], j + 1, depth + 1)
        return count

    return visit(weights[0], 1, 1)


def produce(shard, shards, directory):
    binary = Path(directory) / "search"
    subprocess.run(["g++", "-O3", "-std=c++20", "-fopenmp", "-Wall", "-Wextra", "-Werror",
                    "-o", str(binary), str(ROOT / "search.cpp"), "-lgmpxx", "-lgmp"],
                   check=True, timeout=120)
    proc = subprocess.run([str(binary), "solve", str(shard), str(shards), "950"],
                          check=True, capture_output=True, text=True, timeout=1000)
    print(proc.stdout, end="", flush=True)
    lines = proc.stdout.splitlines()
    first = dict(kv.split("=") for kv in lines[0].split())
    output = {k: float(v) if k == "seconds" else int(v)
              for k, v in (kv.split("=") for kv in lines[-1].split())}
    output.update((k, int(v)) for k, v in first.items())
    output["candidate_details"] = [line for line in lines if line.lower().startswith("candidate")]
    if output["candidates"] != len(output["candidate_details"]):
        raise ValueError("lost candidates")
    if (output["complete"] != 1 or output["shard"] != shard or output["shards"] != shards
            or output["done"] != len(range(shard, output["tasks"], shards))):
        raise ValueError("incomplete coverage")
    return output


def main():
    shard, shards = map(int, sys.argv[1:3])
    output = Path(sys.argv[3])
    if not 0 <= shard < shards <= 1024:
        raise ValueError("bad shard parameters")
    check_bounds()
    os.environ.setdefault("OMP_NUM_THREADS", "4")
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as directory:
        result = produce(shard, shards, directory)
    (output / "result.json").write_text(json.dumps(result, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
