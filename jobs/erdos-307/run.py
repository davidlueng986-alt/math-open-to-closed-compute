#!/usr/bin/env python3
"""Run the checked-in Erdős #307 search domains and verify any witness."""

from fractions import Fraction
from math import isqrt
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile


# (support size, minimum largest prime, maximum largest prime, CPU wall budget in seconds)
DOMAINS = (
    (61, 2, 2381, 180),
    (62, 2, 439, 180),
    (63, 2, 397, 120),
    (64, 2, 373, 60),
    (70, 2, 383, 30),
)
JOB_DIRECTORY = Path(__file__).resolve().parent


def is_prime(p):
    return type(p) is int and p >= 2 and all(p % k for k in range(2, isqrt(p) + 1))


def verify_witness(witness):
    p, q = witness["P"], witness["Q"]
    if not p or not q or not all(is_prime(r) for r in p + q):
        raise ValueError("both lists must be nonempty and contain only primes")
    if len(set(p + q)) != len(p) + len(q):
        raise ValueError("the witness repeats a prime")
    a, b = (sum((Fraction(1, r) for r in side), Fraction()) for side in (p, q))
    if a * b != 1:
        raise ValueError("the reciprocal sums do not multiply to 1")
    return {"P": sorted(p), "Q": sorted(q), "sum_P": str(a), "sum_Q": str(b), "product": "1"}


def write_json(path, value):
    temp = path.with_suffix(".tmp")
    temp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temp.replace(path)


def main():
    shard, shards = map(int, sys.argv[1:3])
    out = Path(sys.argv[3])
    if not 0 <= shard < shards <= 256:
        raise ValueError("invalid shard assignment")
    out.mkdir(parents=True, exist_ok=True)
    result = {"shard": shard, "shards": shards, "mathematical_status": "OPEN", "domains": []}
    env = os.environ.copy()
    env.setdefault("OMP_NUM_THREADS", str(min(4, os.cpu_count() or 1)))

    with tempfile.TemporaryDirectory(prefix="erdos-307-") as temporary:
        binary = Path(temporary) / "search"
        subprocess.run([
            "g++", "-std=c++20", "-O3", "-fopenmp", "-Wall", "-Wextra", "-Werror",
            str(JOB_DIRECTORY / "search.cpp"), "-lgmpxx", "-lgmp", "-o", str(binary),
        ], check=True, timeout=120)
        for size, low, high, seconds in DOMAINS:
            command = [str(binary), *map(str, (size, low, high, shard, shards, seconds))]
            proc = subprocess.run(command, capture_output=True, text=True, check=True,
                                  timeout=seconds + 25, env=env)
            domain_result = json.loads(proc.stdout)
            result["domains"].append(domain_result)
            record = {"size": size, "cap": high, "nodes": domain_result["nodes"],
                      "exact_tests": domain_result["exact_tests"],
                      "square_hits": domain_result["square_hits"],
                      "pending": len(domain_result["pending_max_primes"]),
                      "seconds": domain_result["seconds"]}
            print(json.dumps(record), flush=True)
            if "witness" in domain_result:
                witness = verify_witness(domain_result["witness"])
                write_json(out / "witness.json", witness)
                result["mathematical_status"] = "CLOSED YES"
                write_json(out / "result.json", result)
                print(json.dumps({"status": "CLOSED YES", **witness}), flush=True)
                break
            write_json(out / "result.json", result)


if __name__ == "__main__":
    main()
