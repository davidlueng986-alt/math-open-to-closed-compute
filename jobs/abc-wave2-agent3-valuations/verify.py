#!/usr/bin/env python3
"""Exact finite certificates for the Wave 2 valuation-budget reductions.

The universal conclusions have written proofs in REPORT.md. This program
checks finite instances only and deliberately does not certify either open
global estimate.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import gcd, prod
from pathlib import Path


def smallest_prime_factors(bound):
    spf = list(range(bound + 1))
    for p in range(2, bound + 1):
        if spf[p] != p:
            continue
        for n in range(p * p, bound + 1, p):
            if spf[n] == n:
                spf[n] = p
    return spf


def factor(n, spf):
    out = {}
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out[p] = e
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--shard', type=int, default=0)
    ap.add_argument('--shards', type=int, default=1)
    ap.add_argument('--max-c', type=int, default=1200)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    assert args.shards > 0 and 0 <= args.shard < args.shards
    assert args.max_c >= 2
    args.out.mkdir(parents=True, exist_ok=True)
    spf = smallest_prime_factors(args.max_c)
    facts = [factor(n, spf) if n >= 1 else {} for n in range(args.max_c + 1)]
    counts = Counter()
    cube_free_examples = []
    for c in range(2, args.max_c + 1):
        if c % args.shards != args.shard:
            continue
        for a in range(1, c // 2 + 1):
            b = c - a
            if gcd(a, b) != 1:
                continue
            counts['primitive_triples'] += 1
            f = dict(facts[a])
            for d in [facts[b], facts[c]]:
                assert not (f.keys() & d.keys())
                f.update(d)
            R = prod(f)
            U = prod(p ** max(e - 3, 0) for p, e in f.items())
            S = prod(p ** max(3 - e, 0) for p, e in f.items())
            assert R ** 3 * U == a * b * c * S
            counts['cubic_compensation_identities'] += 1
            for k in [1, 2, 3, 4, 5]:
                Uk = prod(p ** max(e - k, 0) for p, e in f.items())
                Sk = prod(p ** max(k - e, 0) for p, e in f.items())
                assert R ** k * Uk == a * b * c * Sk
                counts['general_cutoff_identities'] += 1
            # The exact geometry term is c^2/(ab); cross-multiply only.
            assert c ** 3 * S * a * b == R ** 3 * U * c ** 2
            counts['geometry_identities'] += 1
            if max(f.values()) <= 2:
                assert a * b * c <= R ** 2
                assert c * (c - 1) <= a * b * c
                assert c <= R
                counts['cube_free_global_height_checks'] += 1
                if len(cube_free_examples) < 6:
                    cube_free_examples.append({'a': a, 'b': b, 'c': c, 'R': R})
            # Power-free tradeoff: a >= R^(1/2), exponents <= 3.
            # c <= sqrt(2)*R^(5/4), checked via c^4 <= 4 R^5.
            if max(f.values()) <= 3 and a ** 2 >= R:
                assert c ** 4 <= 4 * R ** 5
                counts['power_free_tradeoff_checks'] += 1

            # An exhaustive partition at epsilon=1/6. All comparisons exact.
            balanced = 4 * a >= c
            moderate = (not balanced) and c ** 6 <= a ** 6 * R
            thin = (not balanced) and c ** 6 > a ** 6 * R
            assert sum([balanced, moderate, thin]) == 1
            counts['regime_partition_checks'] += 1
            if balanced:
                counts['balanced'] += 1
                assert 3 * c ** 3 * S <= 16 * R ** 3 * U
                # Local premise U/S <= R^(3 epsilon)=sqrt(R).
                if U ** 2 <= S ** 2 * R:
                    assert 9 * c ** 6 <= 256 * R ** 7
                    counts['balanced_composition_instances'] += 1
            elif moderate:
                counts['moderate'] += 1
                # Local premise U/S <= R^(2 epsilon)=R^(1/3).
                if U ** 3 <= S ** 3 * R:
                    assert c ** 6 <= 4 * R ** 7
                    counts['moderate_composition_instances'] += 1
            else:
                counts['thin'] += 1
                # Local premise U*c/(S*a) <= R^(3 epsilon)=sqrt(R).
                if (U * c) ** 2 <= (S * a) ** 2 * R:
                    assert c ** 6 <= 4 * R ** 7
                    counts['thin_composition_instances'] += 1
    obstruction = []
    for n in [1, 2, 3, 10, 100, 1000, 10000, 10 ** 6]:
        if n % args.shards != args.shard:
            continue
        # For (1,n,n+1), c^2/(ab) = (n+1)^2/n > n.
        assert (n + 1) ** 2 > n ** 2
        obstruction.append({'a': 1, 'b': n, 'c': n + 1,
                            'geometry_factor_numerator': (n + 1) ** 2,
                            'geometry_factor_denominator': n,
                            'strict_lower_bound': n})
    payload = {
        'task': 'VALUATION-BUDGET', 'agent': 'wave2_agent3',
        'status': 'CHECKED', 'scope': 'finite exact arithmetic only; no open global estimate proved',
        'parameters': {'max_c': args.max_c, 'epsilon_for_regime_checks': '1/6',
                       'shard': args.shard, 'shards': args.shards},
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'counts': dict(sorted(counts.items())),
        'cube_free_examples': cube_free_examples,
        'geometry_obstruction_examples': obstruction,
        'open_obligations': ['W2-A3-PRODUCT-BOUND', 'W2-A3-THIN-BOUND'],
        'original_abc_closed': False,
        'all_checks_passed': True,
    }
    (args.out / 'result.json').write_text(json.dumps(payload, indent=2) + '\n')
    print(json.dumps({'status': payload['status'], 'counts': payload['counts'],
                      'source_sha256': payload['source_sha256']}, sort_keys=True))


if __name__ == '__main__':
    main()
