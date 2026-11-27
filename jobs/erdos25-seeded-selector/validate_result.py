#!/usr/bin/env python3
"""Audit the recorded prefix, independently of the search's CRT recursion.

This validates actual activation, global private witnesses, telescoping
of recorded exact Haar increments, and the stated finite escape. It
does not independently recompute every Haar increment or prove an
infinite budget bound. The search computes those increments by exact CRT.
"""
import hashlib
import json
import math
import sys
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


def prime_factors(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def main():
    data = json.loads(Path(sys.argv[1]).read_text())
    assert data['status'] == 'EXACT_FINITE_TRUNCATION_ONLY'
    assert data['resume'] is None, 'Public replay must start from the seed.'
    assert data['seed'] == [[6, 0], [10, 1], [15, 2]]
    assert data['tie_break'] == 'largest q'
    assert data['termination_reason'] in ('cutoff', 'time_limit_at_exact_prefix')
    limit = data['last_processed']
    assert 389 <= limit <= data['stop']
    rules = [tuple(x) for x in data['seed']]
    selected = []
    used = {q for q, _ in rules}
    # Direct enumeration supplies the seed density, independently of CRT.
    seed_survivors = sum(all((n-a) % q for q, a in rules) for n in range(30))
    delta = Fraction(seed_survivors, 30)
    assert delta == Fraction(2, 3)
    last_n = 21
    hazards = []
    first_escape = None
    nonzero = []
    for row in data['rows']:
        n, q, a = row['n'], row['q'], row['a']
        assert last_n < n <= limit
        assert q not in used and 0 <= a < q and n == q+a and 2*q > n
        assert all((n-b) % d for d, b in rules)
        assert all((r-a) % q for r in selected)
        inc = Fraction(row['increment'])
        assert inc == Fraction(row['eta']) / q
        assert 0 < inc <= Fraction(1, q) and inc <= delta
        hazards.append(inc / delta)
        delta -= inc
        assert delta == Fraction(row['survivor_measure'])
        used.add(q)
        selected.append(n)
        rules.append((q, a))
        last_n = n
        if a:
            nonzero.append({'n': n, 'q': q, 'a': a,
                            'prime_factors': prime_factors(q)})
            if first_escape is None and (q % 5 or a % 5 != 2):
                first_escape = {'n': n, 'q': q, 'a': a}
    assert data['endpoint_count'] == len(selected)
    assert delta == Fraction(data['survivor_measure'])
    assert first_escape == {'n': 389, 'q': 377, 'a': 12}
    assert {k: data['first_escape'][k] for k in ('n', 'q', 'a')} == first_escape
    for row in data['rows']:
        assert sum((n-row['a']) % row['q'] == 0 for n in selected) == 1
    # This is an independent enumeration of every actual integer in the prefix.
    uncovered = [n for n in range(22, limit+1)
                 if not any(q <= n and (n-a) % q == 0 for q, a in rules)]
    assert not uncovered
    # Independently check the first nonzero increment in one full period.
    seed = [tuple(x) for x in data['seed']]
    first = data['rows'][0]
    assert (first['n'], first['q'], first['a']) == (22, 20, 2)
    direct = sum(n % 20 == 2 and all((n-a) % q for q, a in seed)
                 for n in range(60))
    assert Fraction(direct, 60) == Fraction(first['increment']) == Fraction(1, 60)
    with localcontext() as ctx:
        ctx.prec = 60
        dec = lambda f: Decimal(f.numerator) / Decimal(f.denominator)
        h = sum((Decimal(1)/n for n in selected), Decimal(0))
        hx = sum((Decimal(1)/n for n in range(1, limit+1)), Decimal(0))
        hazard_sum = sum(hazards, Fraction(0))
        out = {
            'status': 'PASS_FINITE_PREFIX_ONLY',
            'last_processed': limit,
            'requested_stop': data['stop'],
            'termination_reason': data['termination_reason'],
            'endpoint_count': len(selected),
            'survivor_measure_exact': str(delta),
            'survivor_measure_decimal': str(dec(delta)),
            'harmonic_endpoints_60_digit': str(h),
            'normalized_endpoint_mass_60_digit': str(h/hx),
            'hazard_partial_sum_exact': str(hazard_sum),
            'hazard_partial_sum_decimal': str(dec(hazard_sum)),
            'first_escape': first_escape,
            'nonzero_rules': nonzero,
            'cofinite_prefix_checked': [22, limit],
            'global_privacy': True,
            'original_activation': True,
            'distinct_moduli': True,
            'source_sha256': hashlib.sha256(
                Path(__file__).with_name('rare_fiber_selector.py').read_bytes()).hexdigest(),
            'scope': 'The Haar increments are computed by the exact recursive CRT search. This separate audit checks arithmetic witnesses and telescoping of the recorded rational increments; only the seed and first increment are independently enumerated. No lower bound on the infinite survivor budget, hazard summability, original closure, or Lean verification is asserted.'
        }
    Path(sys.argv[2]).write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({k: out[k] for k in ('status', 'last_processed', 'endpoint_count',
          'survivor_measure_decimal', 'first_escape', 'termination_reason')}, indent=2))


if __name__ == '__main__':
    main()
