#!/usr/bin/env python3
"""Merge and independently verify all shard certificates for Erdős #287.

Usage: merge.py SHARDS_DIR SUMMARY_DIR

Independently verifies:
  1. Exact base closure for 2 <= B <= 500 via Fraction harmonic sums and
     prime-power subset-sum p-adic exclusions.
  2. Deterministic 64-bit covering chain covering 459 .. 2^64 - 1 with zero gaps.
  3. Every Proth certificate (n, k, a_pp, a_p) via Proth's Theorem (1878) and
     exact integer zero-gap interval overlap using e > 2718281828 / 10^9.
"""
from fractions import Fraction
from pathlib import Path
import json
import math
import os
import sys

E_NUM = 2718281828
E_DEN = 1000000000


def prime_power_factors(x: int):
    f = []
    d = 2
    tmp = x
    while d * d <= tmp:
        if tmp % d == 0:
            q = 1
            while tmp % d == 0:
                tmp //= d
                q *= d
            f.append((d, q))
        d += 1
    if tmp > 1:
        f.append((tmp, tmp))
    return f


def is_forced_omitted_py(x: int, B: int) -> bool:
    a_lo = max(2, int((B + 1) * 1000000 // 7389057))
    for p, q in prime_power_factors(x):
        if q * p <= B:
            continue
        m = B // q
        if m >= p:
            continue
        Lm = math.lcm(*range(1, m + 1))
        Nm = sum(Lm // h for h in range(1, m + 1))
        if p > Nm:
            return True
        h_target = x // q
        h_min = max(1, (a_lo + q - 1) // q)
        reach = {(Lm // h_target) % p}
        for h in range(h_min, m + 1):
            if h == h_target:
                continue
            add = (Lm // h) % p
            reach = reach | {(r + add) % p for r in reach}
        if 0 not in reach:
            return True
    return False


def verify_base(B_max: int = 500) -> dict:
    killed_B = 0
    killed_pair = 0
    for B in range(2, B_max + 1):
        if is_forced_omitted_py(B, B):
            killed_B += 1
            continue
        s = Fraction(0)
        x_lo = 2
        for n in range(B, 1, -1):
            s += Fraction(1, n)
            if s >= 1:
                x_lo = n + 1
                break
        prev = False
        ok = False
        for x in range(x_lo, B):
            cur = is_forced_omitted_py(x, B)
            if cur and prev:
                ok = True
                break
            prev = cur
        if not ok:
            raise AssertionError(f"Base verification failed at B={B}")
        killed_pair += 1
    return {"B_max": B_max, "killed_by_B_forbidden": killed_B, "killed_by_pair": killed_pair}


def is_prime64(n: int) -> bool:
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n == p:
            return True
        if n % p == 0:
            return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
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


def main() -> None:
    shards_dir, summary_dir = Path(sys.argv[1]), Path(sys.argv[2])
    summary_dir.mkdir(parents=True, exist_ok=True)
    shard_files = sorted(shards_dir.glob("shard-*/result.json"))
    if not shard_files:
        sys.exit("no shard results found")

    expected_shards = int(float(os.environ.get("SHARDS", len(shard_files))))
    parts = {}
    for f in shard_files:
        data = json.loads(f.read_text(encoding="utf-8"))
        s = int(data["shard"])
        if int(data["shards"]) != expected_shards:
            sys.exit(f"shard {s} reports shards={data['shards']} != {expected_shards}")
        parts[s] = data

    missing_shards = [s for s in range(expected_shards) if s not in parts]
    if 0 not in parts or "chain64" not in parts[0]:
        sys.exit("shard 0 (base + chain64) missing")

    # 1. Independently verify base [2, 500]
    base_check = verify_base(500)
    covered = 500

    # 2. Independently verify 64-bit chain
    chain64_links = parts[0]["chain64"]["links"]
    for link in chain64_links:
        pp, p = int(link["p_prime"]), int(link["p"])
        assert pp >= 139 and p == 2 * pp - 1
        assert is_prime64(pp) and is_prime64(p)
        lo = p + 2
        hi = (p - 1) * E_NUM // E_DEN
        assert lo <= covered + 1, f"chain64 gap at p={p}"
        covered = max(covered, hi)
    cov64 = covered
    assert cov64 >= (1 << 64) - 1, "chain64 did not reach 2^64 - 1"

    # 3. Collect and independently verify all Proth certificates
    n_min = int(parts[0]["n_min"])
    n_max = int(parts[0]["n_max"])
    certs_by_n = {}
    pending_all = []
    total_proth_tests = 0
    total_seconds = 0.0

    for s, data in sorted(parts.items()):
        assert int(data["n_min"]) == n_min and int(data["n_max"]) == n_max
        proth = data["proth"]
        total_proth_tests += int(proth["total_proth_tests"])
        total_seconds += float(proth["seconds"])
        pending_all.extend(int(x) for x in proth["pending"])
        for c in proth["certs"]:
            n = int(c["n"])
            k = int(c["k"])
            a_pp = int(c["a_pp"])
            a_p = int(c["a_p"])
            assert k % 2 == 1 and k < (1 << n), f"Proth bound failed at n={n}"
            pp = (k << n) + 1
            p = (k << (n + 1)) + 1
            assert pp >= 139 and p == 2 * pp - 1
            assert pow(a_pp, (pp - 1) // 2, pp) == pp - 1, f"Proth p' failed at n={n}"
            assert pow(a_p, (p - 1) // 2, p) == p - 1, f"Proth p failed at n={n}"
            certs_by_n[n] = {"n": n, "k": k, "a_pp": a_pp, "a_p": a_p}

    # 4. Stitch contiguous zero-gap coverage from cov64 upward
    highest_contiguous_n = n_min - 1
    first_gap_n = None
    for n in range(n_min, n_max + 1):
        if n not in certs_by_n:
            first_gap_n = n
            break
        c = certs_by_n[n]
        p = (c["k"] << (n + 1)) + 1
        lo = p + 2
        hi = (p - 1) * E_NUM // E_DEN
        if lo > covered + 1:
            first_gap_n = n
            break
        covered = max(covered, hi)
        highest_contiguous_n = n

    all_covered = (not missing_shards) and (not pending_all) and (first_gap_n is None)
    log10_bound = math.log10(covered)
    digits = len(str(covered))

    report = {
        "problem": "Erdős #287 (JSP-000244)",
        "mathematical_status": "OPEN (unconditional finite lower bound extended; not a global proof)",
        "shards_expected": expected_shards,
        "shards_present": len(parts),
        "missing_shards": missing_shards,
        "base_verified": base_check,
        "chain64_links_verified": len(chain64_links),
        "chain64_exceeds_2_64": cov64 >= (1 << 64) - 1,
        "proth_n_range": [n_min, n_max],
        "proth_certs_verified": len(certs_by_n),
        "highest_contiguous_n": highest_contiguous_n,
        "first_gap_n": first_gap_n,
        "pending_exponents": sorted(set(pending_all)),
        "total_proth_tests": total_proth_tests,
        "total_shard_wall_seconds": round(total_seconds, 3),
        "unconditional_lower_bound_digits": digits,
        "unconditional_lower_bound_log10": round(log10_bound, 4),
        "all_exponents_closed_zero_gap": all_covered,
    }
    (summary_dir / "erdos-287-sieve.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8"
    )
    (summary_dir / "certificates.json").write_text(
        json.dumps({
            "chain64": chain64_links,
            "proth": [certs_by_n[n] for n in sorted(certs_by_n)],
        }, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(report, indent=2))
    sys.exit(0 if all_covered else 1)


if __name__ == "__main__":
    main()
