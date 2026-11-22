#!/usr/bin/env python3
"""Run one shard of the Erdős #647 segmented wheel sieve and independently verify any witness."""

from math import gcd
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile

JOB_DIRECTORY = Path(__file__).resolve().parent

# Default search range: exact 2026 bentrd frontier (9.17447118588e18) to 10^21.
DEFAULT_N_START = 9_174_471_185_880_000_000
DEFAULT_N_END = 1_000_000_000_000_000_000_000  # 10^21
DEFAULT_BUDGET_SECONDS = 18_000  # 5h safety cap below GitHub's 330m/360m limit
WHEEL_W = 10_708_457_760


def is_prime_py(n: int) -> bool:
    """Deterministic Miller-Rabin for all n < 3.317e24 (Sorenson & Webster 2017)."""
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    for p in small:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _pollard_rho_py(n: int) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    for c in range(1, 200):
        x, y, d = 2, 2, 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = gcd(abs(x - y), n)
        if d != n:
            return d
    d = 5
    while d * d <= n:
        if n % d == 0:
            return d
        d += 2
    return n


def exact_tau_py(n: int) -> int:
    """Independent pure-Python exact divisor count tau(n)."""
    if n <= 1:
        return 1
    tau = 1
    e = 0
    while n % 2 == 0:
        n //= 2
        e += 1
    if e:
        tau *= e + 1
    d = 3
    while d <= 1000 and d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            tau *= e + 1
        d += 2
    if n == 1:
        return tau
    if is_prime_py(n):
        return tau * 2
    factors = []
    stack = [n]
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_prime_py(m):
            factors.append(m)
        else:
            f = _pollard_rho_py(m)
            stack.append(f)
            stack.append(m // f)
    factors.sort()
    i = 0
    while i < len(factors):
        j = i + 1
        while j < len(factors) and factors[j] == factors[i]:
            j += 1
        tau *= j - i + 1
        i = j
    return tau


def max_tau_upper_bound_py(n: int) -> int:
    if n <= 10**6:
        return 240
    if n <= 10**12:
        return 6_720
    if n <= 10**18:
        return 103_680
    if n <= 10**19:
        return 161_280
    if n <= 10**20:
        return 245_760
    if n <= 10**21:
        return 368_640
    if n <= 10**22:
        return 552_960
    if n <= 10**23:
        return 860_160
    return 2_000_000


def verify_witness_py(n_str: str) -> dict:
    """Independent exact Python verification of a candidate witness n > 24."""
    n = int(n_str)
    if n <= 24:
        raise ValueError(f"witness must satisfy n > 24, got {n}")
    k_limit = min(n - 1, max_tau_upper_bound_py(n))
    for k in range(1, k_limit + 1):
        t = exact_tau_py(n - k)
        if t > k + 2:
            raise ValueError(f"candidate n={n} failed at k={k}: tau(n-k)={t} > {k+2}")
    return {
        "n": str(n),
        "verified_k_max": k_limit,
        "status": "CLOSED YES",
    }


def write_json(path: Path, value: dict) -> None:
    temp = path.with_suffix(".tmp")
    temp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temp.replace(path)


def main() -> None:
    shard, shards = map(int, sys.argv[1:3])
    out = Path(sys.argv[3])
    if not (0 <= shard < shards <= 256):
        raise ValueError(f"invalid shard assignment: {shard}/{shards}")
    out.mkdir(parents=True, exist_ok=True)

    n_start = int(os.environ.get("ERDOS647_N_START", str(DEFAULT_N_START)))
    n_end = int(os.environ.get("ERDOS647_N_END", str(DEFAULT_N_END)))
    budget = int(os.environ.get("ERDOS647_BUDGET_SECONDS", str(DEFAULT_BUDGET_SECONDS)))

    env = os.environ.copy()
    env.setdefault("OMP_NUM_THREADS", str(min(4, os.cpu_count() or 1)))

    with tempfile.TemporaryDirectory(prefix="erdos-647-") as tmp:
        binary = Path(tmp) / "search"
        subprocess.run(
            [
                "g++", "-std=c++17", "-O3", "-march=native", "-fopenmp",
                "-Wall", "-Wextra", "-Werror",
                str(JOB_DIRECTORY / "search.cpp"), "-o", str(binary),
            ],
            check=True,
            timeout=120,
        )
        # Always run built-in selftest before scanning
        st_proc = subprocess.run([str(binary), "--selftest"], capture_output=True, text=True, check=True, timeout=60)
        selftest_info = json.loads(st_proc.stdout)
        if selftest_info.get("selftest") != "PASS":
            raise RuntimeError(f"selftest failed: {selftest_info}")

        proc = subprocess.run(
            [str(binary), str(n_start), str(n_end), str(shard), str(shards), str(budget), "1"],
            capture_output=True,
            text=True,
            check=True,
            timeout=budget + 120,
            env=env,
        )
        if proc.stderr:
            print(proc.stderr, end="", file=sys.stderr, flush=True)
        result = json.loads(proc.stdout)
        result["selftest"] = selftest_info
        result["mathematical_status"] = "OPEN"

        if "witness_n" in result:
            witness = verify_witness_py(result["witness_n"])
            result["mathematical_status"] = "CLOSED YES"
            result["witness"] = witness
            write_json(out / "witness.json", witness)
            print(json.dumps({"status": "CLOSED YES", **witness}), flush=True)

        write_json(out / "result.json", result)
        print(
            json.dumps({
                "shard": shard,
                "shards": shards,
                "complete": result["complete"],
                "u_tested": result["u_tested"],
                "prime7_survivors": result["prime7_survivors"],
                "max_depth": result["max_depth"],
                "seconds": round(result["seconds"], 3),
                "effective_n_per_sec": result["effective_n_per_sec"],
            }),
            flush=True,
        )


if __name__ == "__main__":
    main()
