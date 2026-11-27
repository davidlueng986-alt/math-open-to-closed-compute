#!/usr/bin/env python3
"""Exact finite audit for the Gaussian ROOT family; no abc closure claim."""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path


def factor(n: int) -> dict[int, int]:
    """Complete trial division, used only for the explicitly small sample."""
    n = abs(n)
    assert n > 0
    result: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def product_factorization(f: dict[int, int]) -> int:
    return math.prod(p ** e for p, e in f.items())


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    max_index = 1001
    u, v = 1, 0
    values = [(u, v)]
    root_count = 0
    samples = []
    for k in range(1, max_index + 1):
        old_u, old_v = u, v
        u, v = old_u - 2 * old_v, 2 * old_u + old_v
        values.append((u, v))
        assert u * u + v * v == 5 ** k
        assert u % 2 == 1 and v % 2 == 0
        assert (u - 2 * v) % 5 == pow(2, k, 5)
        assert math.gcd(u, v) == 1
        assert u % 5 != 0 and v % 5 != 0
        if k % 2 == 0:
            continue
        a, b, c = u * u, v * v, 5 ** k
        assert a > 0 and b > 0 and a + b == c
        assert math.gcd(a, b) == 1
        assert c % 2 == 1 and math.isqrt(c) ** 2 != c
        assert math.isqrt(a) ** 2 == a and math.isqrt(b) ** 2 == b
        # K_2(a)=K_2(b)=1 and K_2(c)=5 via these exact square certificates.
        assert c == 5 * (5 ** ((k - 1) // 2)) ** 2
        # The j numerator is a 5-adic unit; denominator valuation is exactly 2k.
        j_factor = a * a + a * b + b * b
        assert j_factor % 5 == (a * a) % 5 != 0
        assert (a * a * b * b) % 5 != 0
        assert 2 * abs(u * v) <= c
        root_count += 1
        if k <= 21:
            fu, fv = factor(u), factor(v)
            for f in [fu, fv]:
                assert all(is_prime(p) and e > 0 for p, e in f.items())
            assert product_factorization(fu) == abs(u)
            assert product_factorization(fv) == abs(v)
            assert set(fu).isdisjoint(fv)
            assert 5 not in fu and 5 not in fv
            radical_uv = math.prod(fu) * math.prod(fv)
            radical_abc = 5 * radical_uv
            samples.append({
                "k": k, "u": u, "v": v, "a": a, "b": b, "c": c,
                "factor_abs_u": fu, "factor_abs_v": fv,
                "radical_abc": radical_abc,
                "coordinate_squarefree_kernels": [1, 1, 5],
                "j_5_adic_valuation": -2 * k,
            })
    for k in range(1, 201):
        u, v = values[k]
        u2, v2 = values[2 * k]
        assert u2 == u * u - v * v and v2 == 2 * u * v
        assert ((u*u-v*v)**2, 4*u*u*v*v, 5**(2*k)) == (u2*u2, v2*v2, 5**(2*k))
    source_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    certificates = {
        "scope": "Completely factored small sample only; no large-index factorization claim.",
        "small_sample": samples,
    }
    cert_bytes = (json.dumps(certificates, indent=2, sort_keys=True) + "\n").encode()
    (args.out / "certificates.json").write_bytes(cert_bytes)
    result = {
        "status": "CHECKED",
        "source_sha256": source_hash,
        "max_index": max_index,
        "odd_root_indices_checked": root_count,
        "norm_parity_gcd_congruence_checks": max_index,
        "exact_j_5_adic_checks": root_count,
        "doubling_identities_checked": 200,
        "small_complete_factorizations": len(samples),
        "certificates_sha256": hashlib.sha256(cert_bytes).hexdigest(),
        "large_index_radicals_computed": False,
        "original_abc_closed": False,
        "new_global_core_estimates_proved": 0,
        "scope": "Finite exact checks of stated structural family; universal proof is in REPORT.md.",
    }
    (args.out / "result.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
