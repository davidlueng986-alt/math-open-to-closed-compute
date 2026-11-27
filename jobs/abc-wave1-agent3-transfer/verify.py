#!/usr/bin/env python3
"""Exact symbolic checks for ABC Wave 1 Agent 3; these do not prove arithmetic abc."""
import argparse
import hashlib
import json
import platform
import random
from fractions import Fraction
from pathlib import Path

import sympy as sp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--outdir", required=True)
    parser.add_argument("--shard", type=int, default=0)
    parser.add_argument("--shards", type=int, default=1)
    args = parser.parse_args()
    if args.shards != 1 or args.shard != 0:
        raise SystemExit("This exact audit is a single-shard job; use SHARD=0 SHARDS=1.")
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    x = sp.Symbol("x")
    P = lambda z: sp.Poly(z, x, domain=sp.QQ)
    pairs = [(P(x**m), P((x - 1)**n)) for m in range(1, 10) for n in range(1, 10)]
    pairs += [(P(x**m), P(1)) for m in range(1, 21)]
    rng = random.Random(20261127)
    for _ in range(240):
        aa = [rng.randint(-3, 3) for _ in range(rng.randint(2, 7))]
        bb = [rng.randint(-3, 3) for _ in range(rng.randint(2, 7))]
        pairs.append((P(sum(a * x**i for i, a in enumerate(aa))),
                      P(sum(b * x**i for i, b in enumerate(bb)))))
    checked = []
    skipped = 0
    for A, B in pairs:
        C = A + B
        if any(F.is_zero for F in (A, B, C)) or A.gcd(B).degree() != 0:
            skipped += 1
            continue
        W = A.diff() * B - A * B.diff()
        if W.is_zero:
            skipped += 1
            continue
        assert A.gcd(C).degree() == B.gcd(C).degree() == 0
        assert W == A.diff() * C - A * C.diff()
        assert -W == B.diff() * C - B * C.diff()
        ABC = A * B * C
        radical_poly = ABC.sqf_part().monic()
        excess = ABC.exquo(radical_poly)
        assert W.rem(excess).is_zero
        assert max(A.degree(), B.degree(), C.degree()) < radical_poly.degree()
        checked.append({"A": str(A.as_expr()), "B": str(B.as_expr()),
                        "C": str(C.as_expr()), "radical_degree": radical_poly.degree(),
                        "wronskian_degree": W.degree()})
    assert len(checked) > 200

    # F(T)=T(T+1) is squarefree and Resultant(T,T+1)=1, yet specialization
    # at n=2^m can have an arbitrarily high 2-adic multiplicity.
    assert P(x * (x + 1)).sqf_part().degree() == 2
    assert sp.resultant(x, x + 1, x) == 1
    specializations = []
    for m in range(1, 41):
        n = 2**m
        fac = {int(p): int(e) for p, e in sp.factorint(n * (n + 1)).items()}
        rad = sp.prod(fac)
        assert sp.prod(p**e for p, e in fac.items()) == n * (n + 1)
        assert all(sp.isprime(p) for p in fac)
        assert fac[2] == m
        assert sp.gcd(n, n + 1) == 1
        assert rad <= 2 * (n + 1) <= 4 * n
        if m >= 5:
            assert rad**2 < n**3
        specializations.append({"m": m, "n": n, "radical": int(rad), "factors": fac})

    # Scalar shadow ONLY, not a model completeness theorem about IUT.
    scalar_checks = []
    for ell in list(sp.primerange(5, 50)):
        ell = int(ell)
        count = (ell - 1) // 2
        s = sum((Fraction(j*j, count) for j in range(1, count + 1)), Fraction())
        assert s == Fraction(ell * (ell + 1), 12)
        assert s > 1
        for a in (Fraction(1, 7), Fraction(1), Fraction(11, 3)):
            threshold = (s - 1) * a
            too_small = threshold / 2
            assert not (-a <= -s*a + too_small)
            assert -a == -s*a + threshold
            assert (-a <= -s*a + threshold) == (threshold >= (s - 1)*a)
        scalar_checks.append({"ell": ell, "average_j_squared": str(s)})

    cert = {"polynomial_cases": checked, "specializations": specializations,
            "scalar_shadow": scalar_checks}
    cert_bytes = json.dumps(cert, sort_keys=True, indent=2).encode()
    (outdir / "certificates.json").write_bytes(cert_bytes)
    result = {
        "job": "abc-wave1-agent3-transfer", "claim_status": "CHECKED",
        "shard": args.shard, "shards": args.shards,
        "scope": "Finite exact symbolic checks; full specialization obstruction is proved in REPORT.md. No verification of IUT or arithmetic abc.",
        "polynomial_cases_checked": len(checked), "polynomial_cases_skipped": skipped,
        "specialization_cases_checked": len(specializations),
        "scalar_shadow_prime_parameters_checked": len(scalar_checks),
        "all_assertions_passed": True,
        "python": platform.python_version(), "sympy": sp.__version__,
        "certificate_sha256": hashlib.sha256(cert_bytes).hexdigest(),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (outdir / "result.json").write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
