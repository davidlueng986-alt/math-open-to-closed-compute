#!/usr/bin/env python3
"""Exact finite checks for ABC Wave2 agent2; no global-bound claim."""
from __future__ import annotations
import argparse
from array import array
from collections import Counter
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import platform

def canonical(a, b, c):
    return (min(a, b), max(a, b), c)

def transform(t):
    a, b, c = t
    return canonical((a-b)**2, 4*a*b, c*c)

def inverse(t):
    a, b, c = t
    odd = a if a % 2 else b
    w, x = math.isqrt(c), math.isqrt(odd)
    if w*w != c or x*x != odd:
        return None
    assert w % 2 == x % 2 == 1 and 0 < x < w
    result = canonical((w+x)//2, (w-x)//2, w)
    assert math.gcd(result[0], result[1]) == 1
    assert transform(result) == t
    return result

def sieve(n):
    spf = array('I', range(n+1))
    for p in range(2, math.isqrt(n)+1):
        if spf[p] == p:
            for m in range(p*p, n+1, p):
                if spf[m] == m:
                    spf[m] = p
    return spf

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--bound', type=int, default=600)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    assert args.bound >= 10
    args.out.mkdir(parents=True, exist_ok=True)
    spf = sieve((2*args.bound)**2)
    def rad(n):
        assert 0 < n < len(spf)
        r = 1
        while n > 1:
            p = spf[n]
            assert n % p == 0
            r *= p
            while n % p == 0:
                n //= p
        return r
    def triple_rad(t):
        a, b, c = t
        assert a > 0 and b > 0 and a+b == c and math.gcd(a,b) == 1
        return rad(a)*rad(b)*rad(c)
    counts = Counter()
    images = set()
    for c in range(3, math.isqrt(args.bound)+1, 2):
        for a in range(1, (c//2)+1):
            b = c-a
            if math.gcd(a,b) == 1:
                images.add(transform((a,b,c)))
    classified = set()
    roots = set()
    witnesses = []
    thresholds = [(1,1), (6,5), (8,5)]
    for c in range(2, args.bound+1):
        for a in range(1, c//2+1):
            b = c-a
            if math.gcd(a,b) != 1:
                continue
            t = (a,b,c)
            counts['primitive_triples'] += 1
            R = triple_rad(t)
            if c % 2:
                counts['odd_c_triples'] += 1
                p = inverse(t)
                assert (p is not None) == (t in images)
                counts['image_classifications'] += 1
                if p is not None:
                    classified.add(t)
                u, depth = t, 0
                chain = [t]
                while (p := inverse(u)) is not None:
                    assert p[2] < u[2]
                    u = p
                    depth += 1
                    chain.append(u)
                roots.add(u)
                v = u
                for _ in range(depth):
                    v = transform(v)
                assert v == t and c == u[2]**(2**depth)
                counts['descent_reconstructions'] += 1
                counts['root_triples' if depth == 0 else 'nonroot_triples'] += 1
                counts['inverse_steps'] += depth
                D = abs(a-b)
                Rnew = triple_rad(transform(t))
                assert math.gcd(D,a*b*c) == 1
                assert Rnew == R*rad(D) and Rnew <= R*c
                counts['image_radical_relations'] += 1
                if depth:
                    witnesses.append({'triple':t, 'root':u, 'depth':depth})
            else:
                counts['even_c_triples'] += 1
                L = a+c
                new = canonical(b*b,4*a*c,L*L)
                assert new[2] % 2 and math.gcd(L,a*b*c) == 1
                Rnew = triple_rad(new)
                assert Rnew == R*rad(L) and Rnew <= R*L
                assert c < L < 2*c
                assert inverse(new) == canonical(a,c,L)
                counts['parity_radical_relations'] += 1
                for r,s in thresholds:
                    if c**s >= R**r:
                        assert new[2]**(r+s) >= Rnew**(2*r)
                        counts['quality_margin_implications'] += 1
    assert images == classified
    counts['image_triples'] = len(images)
    counts['distinct_roots_in_domain'] = len(roots)
    for m in range(100):
        finite_root=(1,4*m+2,4*m+3)
        adjacent_root=(2*m+1,2*m+2,4*m+3)
        assert inverse(finite_root) is None and inverse(adjacent_root) is None
        assert abs(adjacent_root[0]-adjacent_root[1]) == 1
        assert (transform(adjacent_root)[2] == adjacent_root[2]**2)
        counts['explicit_root_family_instances'] += 2
        counts['adjacent_deficit_identity_instances'] += 1
    # Rational model of the composition, not synthetic abc triples.
    for H0 in range(1,8):
        for L0 in range(0,15):
            for n in range(0,5):
                H = (2**n)*H0
                for delta in [Fraction(1,10),Fraction(1,4),Fraction(2,5)]:
                    A = max(Fraction(0), (1-delta)*H0-L0)
                    for W in range(0, min(2*H,25)+1):
                        B = max(Fraction(0), W-max(L0-H0,0)-delta*H)
                        Ln = H+L0-H0-W
                        assert Ln >= (1-2*delta)*H-A-B
                        counts['rational_composition_instances'] += 1
    for k in range(1,101):
        eps=Fraction(k,17)
        eta=eps/(2+eps)
        delta=eps/(2*(1+eps))
        assert 0 < eta < 1 and (1+eta)/(1-eta) == 1+eps
        assert 0 < delta < Fraction(1,2) and 1-2*delta == 1/(1+eps)
        counts['epsilon_conversion_instances'] += 1
    payload={'bound':args.bound,'counts':dict(sorted(counts.items())), 'all_nonroot_witnesses':witnesses, 'exact_checks_passed':True}
    cert=json.dumps(payload,sort_keys=True,separators=(',',':')).encode()
    (args.out/'certificates.json').write_bytes(cert+b'\n')
    result={
        'status':'CHECKED', 'scope':'Exact finite instances and rational algebra models only; no uniform ROOT or COMPENSATED-GROWTH estimate proved by computation.',
        'backend':'Python '+platform.python_version(), 'domain':{'c_max':args.bound,'positive_primitive':True,'a_le_b':True},
        'counts':payload['counts'], 'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'certificate_sha256':hashlib.sha256(cert).hexdigest(),
        'github':{k:os.environ.get(k) for k in ['GITHUB_REPOSITORY','GITHUB_SHA','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT']},
        'unproved':['W2-A2-ROOT-BOUND','W2-A2-GROWTH-BOUND'],
    }
    (args.out/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,sort_keys=True))

if __name__ == '__main__':
    main()
