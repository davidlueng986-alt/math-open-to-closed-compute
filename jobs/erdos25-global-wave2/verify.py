#!/usr/bin/env python3
"""Independent direct-enumeration check of a finite search certificate.

Integer Haar counts and activation are exact. Decimal transcendental values
are independently recomputed numerical diagnostics, not theorem certificates.
There is no claim that an optimizer found the maximum or an infinite family.
"""
import argparse
from decimal import Decimal, localcontext
import json
import math
from pathlib import Path


def verify(path):
    data = json.loads(Path(path).read_text())
    period, cutoff = data["period"], data["cutoff"]
    assert 1 <= cutoff <= period
    rules = data["rules"]
    moduli = [r["q"] for r in rules]
    assert moduli == sorted(set(moduli))
    assert all(2 <= r["q"] <= cutoff and period % r["q"] == 0
               and 0 <= r["a"] < r["q"] for r in rules)
    # These arrays follow different recurrences from the search: full periodic
    # union and activated integer union are built separately, directly.
    covered = bytearray(period)
    killed = bytearray(cutoff + 1)
    counts, harmonic = [], []
    with localcontext() as ctx:
        ctx.prec = 60
        one = Decimal(1)
        total = sum((one / n for n in range(1, cutoff + 1)), Decimal(0))
        for rule in rules:
            q, a = rule["q"], rule["a"]
            count = 0
            for residue in range(a, period, q):
                if not covered[residue]:
                    covered[residue] = 1
                    count += 1
            weight = Decimal(0)
            # First active point is a+q, including q when a=0.
            for n in range(a + q, cutoff + 1, q):
                if not killed[n]:
                    killed[n] = 1
                    weight += one / n
            assert count == rule["first_kill_count"], (q, count, rule)
            assert abs(float(weight) - rule["harmonic_first_kill"]) < 1e-10
            assert count or weight == 0
            counts.append(count)
            harmonic.append(weight)
        numerator = sum(counts)
        assert numerator == sum(covered) == data["haar_union_numerator"]
        beta = Decimal(numerator) / period
        deleted = sum(harmonic, Decimal(0))
        direct_deleted = sum((one / n for n in range(1, cutoff + 1) if killed[n]), Decimal(0))
        assert abs(deleted - direct_deleted) < Decimal("1e-50")
        energy = sum((Decimal(c) / period * Decimal(r["q"]).ln()
                      for c, r in zip(counts, rules)), Decimal(0))
        entropy = Decimal(0)
        for count, weight in zip(counts, harmonic):
            if weight:
                c, e = weight / total, Decimal(count) / period
                if c > e:
                    entropy += c * (c / e).ln()
        discrepancy = deleted - beta * total
        ratio = max(Decimal(0), discrepancy) ** 2 / (total * (1 + energy))
        values = {
            "harmonic_total": total, "harmonic_deleted": deleted,
            "beta": beta, "first_kill_energy": energy,
            "discrepancy": discrepancy, "energy_ratio": ratio,
            "normalized_disjoint_entropy": entropy,
        }
        for key, value in values.items():
            assert math.isclose(float(value), data[key], rel_tol=1e-9, abs_tol=1e-10), (key, value, data[key])
        return {
            "schema": 1,
            "status": "VERIFIED_FINITE_CANDIDATE_ONLY",
            "period": period, "cutoff": cutoff, "rule_count": len(rules),
            "haar_union_numerator": numerator,
            "haar_union_denominator": period,
            "activated_integer_count": sum(killed),
            "checks": ["distinct normalized rules", "exact Haar first-kill counts",
                       "independent original activation", "all reported scalar diagnostics"],
            "decimal_precision": ctx.prec,
            "metrics": {key: str(value) for key, value in values.items()},
            "limitations": ["restricted divisor family", "finite cutoff",
                            "heuristic search, no optimality claim",
                            "numeric diagnostics do not settle any universal constant",
                            "no proof or counterexample for the infinite problem"],
        }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate")
    parser.add_argument("output")
    args = parser.parse_args()
    result = verify(args.candidate)
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "period", "cutoff", "rule_count")}))


if __name__ == "__main__":
    main()
