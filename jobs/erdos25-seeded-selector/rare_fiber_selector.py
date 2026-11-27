#!/usr/bin/env python3
"""Exact probe of one fixed private-endpoint rule, not an asymptotic proof.

Seed: (6,0), (10,1), (15,2). Start at n=22. At each old survivor,
minimize the exact full Haar increment among unused n/2 < q <= n
whose normalized root n-q is not an earlier selected endpoint.
Break ties in favor of the larger q. The rule has no cutoff parameter;
--stop merely truncates its evaluation.
"""

import argparse
import json
import math
import time
from collections import Counter
from fractions import Fraction
from functools import lru_cache


@lru_cache(maxsize=None)
def factor(n):
    ans = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            z = 1
            while n % p == 0:
                z *= p
                n //= p
            ans.append((p, z))
        p += 1
    if n > 1:
        ans.append((n, n))
    return tuple(ans)


def canonical(classes):
    kept = []
    for q, a in sorted(set(classes)):
        if q == 1:
            return ((1, 0),)
        if not any(q % d == 0 and a % d == b for d, b in kept):
            kept.append((q, a))
    return tuple(kept)


DEADLINE = None


class TimeLimit(Exception):
    pass


def check_clock():
    if DEADLINE is not None and time.monotonic() >= DEADLINE:
        raise TimeLimit


def union_measure(classes):
    """Factor independent prime-power cylinders before the cached CRT core."""
    check_clock()
    if not classes:
        return Fraction(0)
    if classes[0][0] == 1:
        return Fraction(1)
    if len(classes) == 1:
        return Fraction(1, classes[0][0])
    incidence = Counter(p for q, _ in classes for p, _ in factor(q))
    rest = []
    survival_factor = Fraction(1)
    for q, a in classes:
        fs = factor(q)
        if len(fs) == 1 and incidence[fs[0][0]] == 1:
            survival_factor *= Fraction(q-1, q)
        else:
            rest.append((q, a))
    if len(rest) != len(classes):
        return 1 - survival_factor * (1 - union_measure(tuple(rest)))
    return union_core(classes)


@lru_cache(maxsize=200000)
def union_core(classes):
    check_clock()
    powers = {}
    incidence = Counter()
    for q, _ in classes:
        for p, pe in factor(q):
            powers[p] = max(powers.get(p, 1), pe)
            incidence[p] += 1
    p = max(powers, key=lambda x: (incidence[x], -powers[x]))
    pe = powers[p]
    branches = Counter()
    for x in range(pe):
        row = []
        for q, a in classes:
            z = 1
            while q % (z * p) == 0:
                z *= p
            if x % z == a % z:
                r = q // z
                row.append((r, a % r))
        branches[canonical(row)] += 1
    return sum((Fraction(m, pe) * union_measure(row)
                for row, m in branches.items()), Fraction(0))


def conditional_survival(rules, n, q):
    induced = []
    for d, a in rules:
        g = math.gcd(d, q)
        if (a - n) % g:
            continue
        r = d // g
        if r == 1:
            return Fraction(0)
        b = (((a - n) // g) * pow(q // g, -1, r)) % r
        induced.append((r, b))
    return 1 - union_measure(canonical(induced))


def main():
    global DEADLINE
    ap = argparse.ArgumentParser()
    ap.add_argument("--stop", type=int, default=120)
    ap.add_argument("--output", required=True)
    ap.add_argument("--seconds", type=float, default=0,
                    help="Stop cleanly at an exact prefix; zero means no limit.")
    ap.add_argument("--resume", help="Resume a recorded exact prefix JSON.")
    ap.add_argument("--stop-on-escape", action="store_true",
                    help="Stop when a nonzero new class is not inside [2]_5.")
    args = ap.parse_args()
    started = time.monotonic()
    rules = [(6, 0), (10, 1), (15, 2)]
    used = {q for q, _ in rules}
    endpoints = set()
    delta = 1 - union_measure(canonical(rules))
    h = 0.0
    rows = []
    last_processed = 21
    if args.resume:
        with open(args.resume, encoding="utf-8") as f:
            prev = json.load(f)
        assert prev["seed"] == [[6, 0], [10, 1], [15, 2]]
        assert prev["tie_break"] == "largest q"
        for row in prev["rows"]:
            n, q, a = row["n"], row["q"], row["a"]
            assert n > last_processed and n == q + a and n/2 < q <= n
            assert q not in used and a not in endpoints
            assert all((n-b) % d for d, b in rules)
            assert all((r-a) % q for r in endpoints)
            e = conditional_survival(rules, n, q) / q
            assert e == Fraction(row["increment"])
            delta -= e
            assert delta == Fraction(row["survivor_measure"])
            rules.append((q, a))
            used.add(q)
            endpoints.add(n)
            rows.append(row)
            h += 1.0/n
            last_processed = n
        last_processed = prev.get("last_processed", prev["stop"])
    if args.seconds:
        DEADLINE = time.monotonic() + args.seconds
    reason = "cutoff"
    first_escape = next((row for row in rows
                         if row["a"] and (row["q"] % 5 or row["a"] % 5 != 2)), None)
    try:
        for n in range(last_processed + 1, args.stop + 1):
            check_clock()
            if any((n - a) % q == 0 for q, a in rules):
                last_processed = n
                continue
            best = None
            for q in range(n, n // 2, -1):
                check_clock()
                if q in used or n - q in endpoints:
                    continue
                eta = conditional_survival(rules, n, q)
                assert eta > 0
                e = eta / q
                if best is None or e < best[0]:
                    best = (e, q, eta)
            if best is None:
                last_processed = n
                continue
            e, q, eta = best
            a = n - q
            assert 0 <= a < q and q <= n < 2 * q
            assert all((r - a) % q for r in endpoints)
            rules.append((q, a))
            used.add(q)
            endpoints.add(n)
            delta -= e
            h += 1.0 / n
            row = {"n": n, "q": q, "a": a, "eta": str(eta),
                   "increment": str(e), "survivor_measure": str(delta),
                   "harmonic_endpoints": h}
            rows.append(row)
            last_processed = n
            print(json.dumps({**row, "survivor_decimal": float(delta)}), flush=True)
            if a and (q % 5 or a % 5 != 2):
                if first_escape is None:
                    first_escape = row
                if args.stop_on_escape:
                    reason = "first_escape"
                    break
    except TimeLimit:
        reason = "time_limit_at_exact_prefix"
    DEADLINE = None
    # Independent direct CRT enumeration when the whole period is modest.
    L = math.lcm(*(q for q, _ in rules))
    if L <= 2_000_000:
        count = sum(not any((n-a) % q == 0 for q, a in rules)
                    for n in range(L))
        assert delta == Fraction(count, L)
    for row in rows:
        assert [n for n in endpoints if (n-row["a"]) % row["q"] == 0] == [row["n"]]
    out = {"status": "EXACT_FINITE_TRUNCATION_ONLY", "stop": args.stop,
           "last_processed": last_processed, "termination_reason": reason,
           "seconds": time.monotonic() - started,
           "seed": [[6, 0], [10, 1], [15, 2]], "first_endpoint": 22,
           "tie_break": "largest q", "rows": rows,
           "survivor_measure": str(delta), "period_bits": L.bit_length(),
           "endpoint_count": len(rows), "harmonic_endpoints": h,
           "normalized_endpoint_mass": h / sum(1.0/n for n in range(1, last_processed+1)),
           "first_escape": first_escape,
           "resume": args.resume,
           "resume_validation": "selected increments and privacy rechecked exactly; prior argmin choices rely on the recorded run" if args.resume else None,
           "cache": str(union_core.cache_info())}
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
        f.write("\n")


if __name__ == "__main__":
    main()
