#!/usr/bin/env python3
"""Exact algebraic audit; does not prove the imported finiteness theorem."""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
import json, os, platform


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(a, b):
    return trim([(a[i] if i < len(a) else 0) +
                 (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def scale(a, c):
    return trim([c*x for x in a])


def mul(a, b):
    p = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            p[i+j] += x*y
    return trim(p)


def square(a):
    return mul(a, a)


def factor(n):
    assert 1 <= n <= 10**7
    out = []
    p = 2
    while p*p <= n:
        e = 0
        while n % p == 0:
            e += 1
            n //= p
        if e:
            out.append((p, e))
        p = 3 if p == 2 else p+2
    if n > 1:
        out.append((n, 1))
    return out


def ec_add(P, Q):
    if P is None:
        return Q
    if Q is None:
        return P
    x, y = P
    u, v = Q
    assert y*y == x*x*x+4*x*x+2*x
    assert v*v == u*u*u+4*u*u+2*u
    if x == u and y == -v:
        return None
    slope = (3*x*x+8*x+2)/(2*y) if P == Q else (v-y)/(u-x)
    w = slope*slope-4-x-u
    z = -y+slope*(x-w)
    assert z*z == w*w*w+4*w*w+2*w
    return w, z


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', default='local-evidence')
    args = ap.parse_args()
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)

    p = [0, 1]
    for _ in range(3):
        p = add(scale(square(p), 2), [-1])
    expected = [1, 0, -32, 0, 160, 0, -256, 0, 128]
    assert p == expected
    q = [0, -8, 0, 80, 0, -192, 0, 128]
    derivative = [i*p[i] for i in range(1, len(p))]
    assert derivative == scale(q, 8)
    certificate = add(square(p), mul([1, 0, -1], square(q)))
    assert certificate == [1]

    counts = {'polynomial_certificates': 3, 'seeds': 0,
              'lucas_trace_identities': 0, 'lucas_product_identities': 0,
              'exact_rank_checks': 0, 'primewise_budgets': 0}
    for v in range(1, 10001):
        assert v//2 <= v-1 <= 2*(v//2)
        counts['primewise_budgets'] += 1

    for c0 in range(3, 32, 2):
        for a0 in range(1, (c0+1)//2):
            b0 = c0-a0
            if gcd(a0, b0) != 1:
                continue
            counts['seeds'] += 1
            d0 = a0-b0
            u, v = 2*d0, c0*c0
            assert gcd(u, v) == 1
            U, V = [0, 1], [2, u]
            for n in range(2, 33):
                U.append(u*U[-1]-v*U[-2])
                V.append(u*V[-1]-v*V[-2])
            d, c, product = d0, c0, 1
            for j in range(5):
                assert V[2**j] == 2*d
                counts['lucas_trace_identities'] += 1
                product *= d
                assert U[2**(j+1)] == 2**(j+1)*product
                counts['lucas_product_identities'] += 1
                D = abs(d)
                assert gcd(d, c) == 1
                if D <= 10**7:
                    for prime, exponent in factor(D):
                        k = 2**(j+1)
                        assert prime != 2
                        assert U[k] % prime == 0
                        assert all(U[n] % prime != 0 for n in range(1, k))
                        assert (U[k] // (prime**exponent)) % prime != 0
                        counts['exact_rank_checks'] += 1
                d, c = 2*d*d-c*c, c*c

    P = (Fraction(-1), Fraction(1))
    point = None
    for _ in range(7):
        point = ec_add(point, P)
    x, y = point
    X = x/y
    Y = (2*x+4)*X*X-1
    assert Y*Y == 8*X**4-8*X*X+1
    d0, c0 = abs(X.numerator), X.denominator
    assert 0 < d0 < c0 and d0 % 2 and c0 % 2
    a0, b0 = (c0-d0)//2, (c0+d0)//2
    assert (a0,b0,c0) == (233930115,10478411804,10712341919)
    assert gcd(a0, b0) == 1
    d, c = a0-b0, c0
    for _ in range(2):
        d, c = 2*d*d-c*c, c*c
    D = abs(d)
    root = isqrt(D)
    assert root*root == D
    assert D == 4936424930851777122654982737863450361601

    certificates = {
        'polynomial_coefficients_low_to_high': p,
        'derivative_divided_by_eight': q,
        'squarefree_identity_coefficients': certificate,
        'witness': {'seed': [a0,b0,c0], 'index': 2, 'difference': d,
                    'absolute_difference': D, 'integer_square_root': root,
                    'elliptic_point_7P': [str(x),str(y)],
                    'quartic_point': [str(X),str(Y)]}}
    cert_bytes = (json.dumps(certificates, sort_keys=True, indent=2)+'\n').encode()
    (out/'certificates.json').write_bytes(cert_bytes)
    result = {
        'status': 'CHECKED', 'problem_status': 'BLOCKED',
        'scope': 'Exact finite algebraic, rank and witness checks only; no proof of Faltings, Darmon-Granville or an asymptotic radical estimate.',
        'counts': counts, 'python': platform.python_version(),
        'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'certificates_sha256': sha256(cert_bytes).hexdigest(),
        'github_run_id': os.getenv('GITHUB_RUN_ID'),
        'github_sha': os.getenv('GITHUB_SHA')}
    (out/'result.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
