#!/usr/bin/env python3
"""Exact finite verification of Wave2 orbit-local structural lemmas.

Only Python's standard library is required. Factoring is exhaustive trial
division and only attempted for positive integers <= 10**8. No finite test
is evidence for the remaining infinite lifting-mass estimate.
"""
import argparse
import hashlib
import json
import math
import os
import platform
from fractions import Fraction
from pathlib import Path

def factor(n):
    assert 1 <= n <= 10**8
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out

def mul(x, y, ab, modulus):
    return ((x[0]*y[0]-ab*x[1]*y[1]) % modulus,
            (x[0]*y[1]+x[1]*y[0]) % modulus)

def power(x, n, ab, modulus):
    r = (1, 0)
    while n:
        if n & 1:
            r = mul(r, x, ab, modulus)
        x = mul(x, x, ab, modulus)
        n >>= 1
    return r

def content_v(pair, p, cap):
    def one(x):
        v = 0
        while v < cap and x % p == 0:
            v += 1
            x //= p
        return v
    return min(map(one, pair))

def lift_root(p, h, exponent):
    zeta, modulus = 2 % p, p
    assert pow(zeta, h, p) == 1 and pow(zeta, h//2, p) == p-1
    for _ in range(1, exponent):
        rem = pow(zeta, h, modulus*p)
        assert (rem-1) % modulus == 0
        digit = (-(rem-1)//modulus * pow(h*pow(zeta, h-1, p), -1, p)) % p
        zeta += digit*modulus
        modulus *= p
        assert pow(zeta, h, modulus) == 1
    return zeta, modulus

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    certs = {'local_valuation': [], 'varying_seed_lifts': [], 'weighted_sums': []}
    counts = {'seeds': 0, 'integer_states': 0, 'fully_factored_differences': 0,
              'prime_valuation_identities': 0, 'repeated_prime_cases': 0,
              'varying_seed_lifts': 0, 'exact_weighted_sum_cases': 0}
    for c0 in range(3, 62, 2):
        for a0 in range(1, (c0+1)//2):
            b0 = c0-a0
            if math.gcd(a0, b0) != 1:
                continue
            counts['seeds'] += 1
            a, b, c = a0, b0, c0
            seen_support = set()
            for j in range(5):
                counts['integer_states'] += 1
                d = a-b
                assert a+b == c and math.gcd(a, b) == 1 and c == c0**(2**j)
                assert d != 0 and d % 2 != 0 and math.gcd(abs(d), a*b*c) == 1
                if abs(d) <= 10**8:
                    fs = factor(abs(d))
                    assert math.prod(p**e for p, e in fs.items()) == abs(d)
                    assert seen_support.isdisjoint(fs)
                    seen_support.update(fs)
                    counts['fully_factored_differences'] += 1
                    for p, e in fs.items():
                        ab = a0*b0
                        legendre = pow((-ab) % p, (p-1)//2, p)
                        chi = 1 if legendre == 1 else -1
                        assert legendre in (1, p-1)
                        h = 2**(j+2)
                        assert (p-chi) % h == 0
                        modulus = p**(e+1)
                        invc = pow(c0, -1, modulus)
                        z = (((a0-b0)*invc) % modulus, (2*invc) % modulus)
                        assert (z[0]*z[0]+ab*z[1]*z[1]) % modulus == 1
                        lhs = power(z, 2**(j+1), ab, modulus)
                        lhs = ((lhs[0]+1) % modulus, lhs[1])
                        scalar = (2*d*pow(c, -1, modulus)) % modulus
                        mid = power(z, 2**j, ab, modulus)
                        assert lhs == ((scalar*mid[0]) % modulus, (scalar*mid[1]) % modulus)
                        assert power(z, h//2, ab, p) == (p-1, 0)
                        w = power(z, p-chi, ab, modulus)
                        difference = ((w[0]-1) % modulus, w[1])
                        assert content_v(difference, p, e+1) == e
                        assert (w[0] % (p**e), w[1] % (p**e)) == (1, 0)
                        counts['prime_valuation_identities'] += 1
                        counts['repeated_prime_cases'] += int(e >= 2)
                        certs['local_valuation'].append({'seed': [a0,b0,c0], 'j': j, 'p': p,
                                                         'valuation': e, 'chi': chi,
                                                         'z_power_mod_next': list(w)})
                a, b, c = d*d, 4*a*b, c*c
    # Construct arbitrarily high valuations at an arbitrary fixed index by
    # changing the seed. These are not a single-seed counterexample sequence.
    for j, p in enumerate([5, 17, 257, 65537, 641]):
        h = 2**(j+2)
        for exponent in range(1, 6):
            zeta, modulus = lift_root(p, h, exponent)
            assert pow(zeta, h//2, modulus) == modulus-1
            x = ((zeta + pow(zeta, -1, modulus))*pow(2, -1, modulus)) % modulus
            b0 = ((1-x)*pow(1+x, -1, modulus)) % modulus
            if b0 % 2:
                b0 += modulus
            assert b0 > 0 and b0 % 2 == 0 and math.gcd(b0+1, p) == 1
            a, b, c = 1, b0, b0+1
            for _ in range(j):
                a, b, c = (a-b)**2, 4*a*b, c*c
            assert (a-b) % modulus == 0 and a != b
            assert math.gcd(a,b) == 1 and c == (b0+1)**(2**j)
            counts['varying_seed_lifts'] += 1
            certs['varying_seed_lifts'].append({'j': j, 'p': p, 'minimum_valuation': exponent,
                                               'seed': [1,b0,b0+1], 'zeta': zeta})
    for n in range(1, 65):
        for mode in range(4):
            es = [(2**j if (mode == 0 or (mode == 1 and j%3 == 0)) else
                   (j if mode == 2 else 0)) for j in range(n)]
            E = sum(es)
            identity = sum((Fraction(2**j, 2**n)*Fraction(es[j], 2**j) for j in range(n)), Fraction())
            assert identity == Fraction(E, 2**n)
            M = max(Fraction(es[j], 2**j) for j in range(n))
            assert Fraction(E, 2**n) <= M*Fraction(2**n-1, 2**n)
            assert Fraction(E, 2**n) >= Fraction(es[-1], 2**n)
            counts['exact_weighted_sum_cases'] += 1
            certs['weighted_sums'].append([n,mode,E])
    payload = json.dumps(certs, sort_keys=True, separators=(',', ':')).encode()
    (args.out/'certificates.json').write_bytes(payload+b'\n')
    result = {'status': 'CHECKED', 'scope': 'finite exact structural checks only; infinite mass remains BLOCKED',
              'python': platform.python_version(), 'counts': counts,
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'certificate_sha256': hashlib.sha256(payload).hexdigest(),
              'github_run_id': os.environ.get('GITHUB_RUN_ID'), 'github_sha': os.environ.get('GITHUB_SHA')}
    (args.out/'result.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
