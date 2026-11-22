#!/usr/bin/env python3
"""Check bounds, run one shard, and save its exact enumeration counts."""

from fractions import Fraction
from math import isqrt, prod
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile

CUTOFF = 2381
Q = 5_000_000
H = 443759330344295771
ROOT = Path(__file__).resolve().parent


def primes_through(cap):
    return [p for p in range(2, cap + 1) if all(p % r for r in range(2, isqrt(p) + 1))]


def check_bounds():
    primes = primes_through(CUTOFF)
    T = [Fraction()]
    for p in primes[:62]:
        T.append(T[-1] + Fraction(1, p))

    def upper_of_pair(lower, upper, mass):
        assert mass < min(lower + 1 / lower, upper + 1 / upper)

    upper_of_pair(Fraction(907, 1000), Fraction(1103, 1000), T[61])
    assert T[62] - Fraction(1, 2) < 2
    assert T[58] + Fraction(3, 2382) < 2
    assert prod(primes[:49]) > Fraction(1103, 1000) * max(CUTOFF**12, CUTOFF**10 * 10**40, CUTOFF**11 * 10**20)
    tiny = Fraction(1, 10**20)
    tau_small = tiny + Fraction(1, CUTOFF + 1)
    tau_large = tiny + Fraction(1, Q + 1)
    for tau, p_cap, forced in [(tau_small, 1190, 157), (tau_large, 794, 167)]:
        assert T[58] + Fraction(1, p_cap + 1) + tau < 2
        assert T[60] - Fraction(1, forced) + tau < 2

    upper_of_pair(Fraction(948, 1000), Fraction(1055, 1000), T[59] + tau_small)
    upper_of_pair(Fraction(951, 1000), Fraction(105, 100), T[59] + tau_large)
    assert Fraction(951, 1000) - tiny > Fraction(95, 100)
    assert Fraction(1, CUTOFF + 1) + tiny < Fraction(((1 << 62) + CUTOFF) // (CUTOFF + 1) + 1, 1 << 62)
    for size, tail_bound in [(10, tau_small), (11, tiny)]:
        cap = sum(Fraction(1, p) for p in primes[1:size + 2])
        for p in [3, 5]:
            assert cap - Fraction(1, p) < Fraction(948, 1000) - tail_bound

    ranks = [min(1190, (60 - j) // (2 - T[j - 1] - tau_small)) for j in range(1, 60)]
    lower = [Fraction(1, p) for p in ranks[-11:]]
    higher = [Fraction(1, p) for p in primes[1:12]]
    lower[:2] = higher[:2]
    remaining = Fraction(948, 1000) - tiny - sum(lower)
    for i, maximum in enumerate(higher):
        amount = max(0, min(remaining, maximum - lower[i]))
        lower[i] += amount
        remaining -= amount
    assert remaining == 0 and int(1 / prod(lower)) == H
    D_min = prod(primes[:59])
    assert D_min > 2 * Q * Fraction(1055, 1000) * H**6
    assert D_min * Fraction(948, 1000) > 2 * H**2


def run_cpp(name, arguments, temp, env, seconds):
    binary = Path(temp) / name
    subprocess.run(["g++", "-O3", "-std=c++20", "-fopenmp", "-Wall", "-Wextra", "-Werror",
                    str(ROOT / f"{name}.cpp"), "-lgmpxx", "-lgmp", "-o", str(binary)],
                   check=True, timeout=120)
    return subprocess.run([str(binary), *map(str, arguments)], capture_output=True,
                          text=True, check=True, timeout=seconds, env=env)


def main():
    shard, shards = map(int, sys.argv[1:3])
    out = Path(sys.argv[3])
    if not 0 <= shard < shards <= 256:
        raise ValueError("invalid shard assignment")
    check_bounds()
    out.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.setdefault("OMP_NUM_THREADS", str(min(4, os.cpu_count() or 1)))
    with tempfile.TemporaryDirectory(prefix="erdos-307-dual61-") as temp:
        same = run_cpp("same", [shard, shards], temp, env, 300)
        opposite = run_cpp("opposite", [shard, shards], temp, env, 600)

    same_rows = []
    candidates = []
    for line in same.stdout.splitlines():
        if line.startswith("CANDIDATE"):
            candidates.append(line)
        elif line.startswith("third="):
            row = {k: int(v) for k, v in (field.split("=") for field in line.split())}
            same_rows.append(row)
    if sorted(row["third"] for row in same_rows) != [7, 11][shard::shards]:
        raise ValueError("incorrect same-side prefix coverage")
    opposite_data = json.loads(opposite.stdout)
    candidates.extend(opposite.stderr.splitlines())
    summary = {"shard": shard, "shards": shards, "same": same_rows, "opposite": opposite_data,
               "candidate_details": candidates}
    if len(candidates) != sum(row["roots"] for row in same_rows) + opposite_data["opposite_candidates"]:
        raise ValueError("unexpected candidate output")
    (out / "result.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
