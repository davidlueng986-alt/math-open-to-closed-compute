#!/usr/bin/env python3
"""Exact certificates for the alternative root-escape proof; no global ABC claim."""
import argparse
import hashlib
import json
import math
from functools import lru_cache
from pathlib import Path
import sympy as s


def square(n):
    return n >= 0 and math.isqrt(n) ** 2 == n


@lru_cache(None)
def support(n):
    n = abs(n)
    assert n > 0
    out = set()
    p = 2
    while p * p <= n:
        if n % p == 0:
            out.add(p)
            while n % p == 0:
                n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        out.add(n)
    return frozenset(out)


def radical_from_support(numbers, known_support):
    return math.prod(p for p in known_support if any(n % p == 0 for n in numbers))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', required=True)
    ap.add_argument('--require-sage', action='store_true')
    args = ap.parse_args()
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    x, t, a, c = s.symbols('x t a c')
    P = -6*x**6 + 25*x**4 - 36*x**2 + 18
    U = 504*x**4 - 572*x**2 + 4
    V = -84*x**5 + 212*x**3 - 145*x
    Q = 6*c*c - 8*a*c + 3*a*a
    exact = {
        'factorization': s.expand(P - (3-2*x*x)*(3*x**4-8*x*x+6)),
        'bezout': s.expand(U*P + V*s.diff(P,x) - 72),
        'elliptic_quotient': s.expand((9-6*x*x)**3 - 2*(9-6*x*x)**2 + 9*(9-6*x*x) - 36*P),
        'cubic_sum': s.expand(a*a*(3*c-2*a) + (c-a)**2*(c+2*a) - c**3),
        'quartic_sum': s.expand(a*a*Q + (c-a)**3*(c+3*a) - c**4),
        'cubic_radical_budget': s.expand((3*c-2*a)*(c+2*a) - (4*c*c-(c-2*a)**2)),
        'quartic_positivity': s.expand(Q - (a*a+4*a*(c-a)+6*(c-a)**2)),
        'quartic_function': s.expand(1-t*t*(6-8*t+3*t*t) - (1-t)**3*(1+3*t)),
    }
    assert all(v == 0 for v in exact.values()), exact
    disc = int(s.discriminant(P,x))
    assert disc == 35831808
    rows = []
    for u in range(3):
        for v in range(3):
            if (u,v) == (0,0):
                continue
            q2 = (2*u**4+4*u*u*v*v-16*v**4) % 3
            qm1 = (-u**4+4*u*u*v*v+32*v**4) % 3
            assert q2 == qm1 == 2
            rows.append({'u':u,'v':v,'class2':q2,'class_minus1':qm1})
    reductions = {}
    for p in [5,7]:
        pts = [(a,b) for a in range(p) for b in range(p)
               if (b*b-a**3+2*a*a-9*a) % p == 0]
        reductions[str(p)] = {'count':len(pts)+1,'affine_points':pts}
    assert reductions['5']['count'] == 4 and reductions['7']['count'] == 12
    # Rational doubling on y²=x³−2x²+9x.
    slope = s.Rational(3*3**2-4*3+9, 2*6)
    xd = slope*slope+2-2*3
    yd = -6+slope*(3-xd)
    assert (xd,yd) == (0,0)

    map_counts = {'odd_primitive_triples':0,'nonroots':0,'cubic_escapes':0,'quartic_needed':0}
    gcd_values = set()
    witnesses = []
    for c0 in range(3,181,2):
        for a0 in range(1,c0,2):
            if math.gcd(a0,c0) != 1:
                continue
            b0 = c0-a0
            map_counts['odd_primitive_triples'] += 1
            q = 6*c0*c0-8*a0*c0+3*a0*a0
            tri3 = (a0*a0*(3*c0-2*a0), b0*b0*(c0+2*a0), c0**3)
            raw4 = (a0*a0*q, b0**3*(c0+3*a0), c0**4)
            g = math.gcd(*raw4)
            tri4 = tuple(n//g for n in raw4)
            assert 81 % g == 0
            gcd_values.add(g)
            old_support = support(a0) | support(b0) | support(c0)
            R = math.prod(old_support)
            S3 = old_support | support(3*c0-2*a0) | support(c0+2*a0)
            S4 = old_support | support(q) | support(c0+3*a0)
            r3 = radical_from_support(tri3,S3)
            r4 = radical_from_support(tri4,S4)
            assert r3 <= 4*R*c0*c0 and r4 <= 24*R*c0**3
            for tri in (tri3,tri4):
                aa,bb,cc = tri
                assert aa+bb == cc and min(tri)>0 and math.gcd(*tri)==1
                assert aa%2 == cc%2 == 1 and bb%2 == 0
            if square(a0) and square(c0):
                map_counts['nonroots'] += 1
                e3 = not(square(tri3[0]) and square(tri3[2]))
                e4 = not(square(tri4[0]) and square(tri4[2]))
                assert e3 or e4
                map_counts['cubic_escapes' if e3 else 'quartic_needed'] += 1
                if not e3:
                    witnesses.append({'input':[a0,b0,c0],'cubic':list(tri3),'quartic':list(tri4),'gcd':g})
    assert map_counts['quartic_needed'] > 0
    sage_data = {'available':False,'required':args.require_sage}
    if args.require_sage:
        from sage.all import EllipticCurve, GF, PolynomialRing, QQ, HyperellipticCurve
        import sage.version
        E = EllipticCurve(QQ,[0,-2,0,9,0])
        Ep = EllipticCurve(QQ,[0,4,0,-32,0])
        ranks = [int(C.rank(proof=True,algorithm='mwrank_lib',use_database=False)) for C in (E,Ep)]
        assert ranks == [0,0]
        torsion = sorted((str(p[0]),str(p[1])) for p in E.torsion_points() if not p.is_zero())
        assert torsion == [('0','0'),('3','-6'),('3','6')]
        assert E.torsion_order() == 4
        S = PolynomialRing(QQ,'z'); z = S.gen()
        assert HyperellipticCurve(-6*z**6+25*z**4-36*z**2+18).genus() == 2
        sage_data = {'available':True,'required':True,'version':sage.version.version,'ranks':ranks,
                     'rank_method':'mwrank_lib, proof=True, use_database=False','E_torsion_affine':torsion,
                     'conductor':int(E.conductor()),'genus':2}
    receipt = {
        'status':'CHECKED','original_problem':'ABC','original_resolution':'unknown',
        'scope':'Exact polynomial/descent certificates, finite arithmetic map regression, optional certified Sage rank. No proof of global ROOT/LOW/CUSP estimates.',
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'symbolic_zero_identities':list(exact),'sextic_discriminant':disc,
        'mod3_complete_nonzero_pairs':rows,'reductions':reductions,
        'map_domain':'all positive primitive odd-c triples with c<=180 and first summand odd',
        'map_counts':map_counts,'quartic_gcd_values':sorted(gcd_values),
        'quartic_needed_witnesses':witnesses,'sage':sage_data,
    }
    (out/'result.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'CHECKED','identities':len(exact),'map_counts':map_counts,'sage':sage_data},sort_keys=True))

if __name__ == '__main__':
    main()
