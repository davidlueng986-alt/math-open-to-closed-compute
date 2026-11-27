#!/usr/bin/env python3
"""Exact finite audit of primitive relation normalization; no asymptotic claim."""
import argparse
import hashlib
import itertools
import json
import math
import os
import platform
from functools import lru_cache
from pathlib import Path

@lru_cache(None)
def radical(n):
    assert n > 0
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            r *= p
            while n % p == 0:
                n //= p
        p = 3 if p == 2 else p + 2
    return r * n if n > 1 else r

def rad_product(*values):
    return math.lcm(*(radical(abs(n)) for n in values))

def normalize(A, B, C, x, y, z):
    raw = [A*x, B*y, C*z]
    assert all(raw) and sum(raw) == 0
    g = math.gcd(*raw)
    a, b, c = sorted(abs(t)//g for t in raw)
    assert a > 0 and a+b == c and math.gcd(a, b) == 1
    return (a, b, c), g

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', required=True)
    args = parser.parse_args()
    out = Path(args.out); out.mkdir(parents=True, exist_ok=True)
    counts = dict(generic_primitive_gcd=0, primitive_relations=0,
                  exact_conditional_exponent=0, abc_embeddings=0,
                  varying_base_obstructions=0, sharp_gcd_witnesses=0)
    digest = hashlib.sha256()
    def record(kind, values):
        counts[kind] += 1
        digest.update((kind + ':' + ','.join(map(str, values)) + '\n').encode())

    small = [-3,-2,-1,1,2,3]
    primitive = [v for v in itertools.product(small, repeat=3) if math.gcd(*v) == 1]
    for A,B,C in itertools.product(range(1,9), repeat=3):
        L = math.lcm(A,B,C)
        for x,y,z in primitive:
            g = math.gcd(A*x,B*y,C*z)
            assert L % g == 0
            record('generic_primitive_gcd',(A,B,C,x,y,z,g))

    coeffs = [i for i in range(-12,13) if i]
    for A,B,C in itertools.product(range(1,10), repeat=3):
        L,m,M,R0 = math.lcm(A,B,C), min(A,B,C), max(A,B,C), rad_product(A,B,C)
        for x,y in itertools.product(coeffs,repeat=2):
            numerator = -A*x-B*y
            if numerator == 0 or numerator % C:
                continue
            z = numerator//C
            if math.gcd(x,y,z) != 1:
                continue
            (a,b,c),g = normalize(A,B,C,x,y,z)
            H = max(abs(x),abs(y),abs(z))
            R,Q = rad_product(a,b,c), rad_product(x,y,z)
            assert L % g == 0 and c*L >= m*H and c <= M*H
            assert R <= R0*Q
            record('primitive_relations',(A,B,C,x,y,z,a,b,c,g))
            # beta=r/s, epsilon=t/u; all powers nonnegative integers.
            for r,s,t,u in [(1,2,1,2),(2,3,1,4),(3,4,1,6)]:
                exponent = s*u-r*(u+t)
                assert exponent > 0
                if Q**s <= H**r:
                    assert c**(s*u)*L**(s*u)*R0**(s*(u+t)) >= m**(s*u)*R**(s*(u+t))*H**exponent
                    record('exact_conditional_exponent',(A,B,C,x,y,z,r,s,t,u))

    fixed_bases = [(1,1,1),(2,3,5),(4,6,9),(8,8,8),(2,8,32),(12,5,18),(7,11,13),(9,4,25)]
    for c in range(2,301):
        for a in range(1,c//2+1):
            b = c-a
            if math.gcd(a,b) != 1:
                continue
            R = rad_product(a,b,c)
            for A,B,C in fixed_bases:
                raw = (B*C*a,A*C*b,-A*B*c)
                d = math.gcd(*raw)
                x,y,z = (v//d for v in raw)
                D = math.lcm(B*C,A*C,A*B)
                M = max(B*C,A*C,A*B)
                H = max(abs(x),abs(y),abs(z))
                assert D % d == 0 and (A*B*C) % d == 0
                assert math.gcd(x,y,z) == 1 and A*x+B*y+C*z == 0
                assert D*H >= A*B*c and H <= M*c
                assert rad_product(x,y,z) <= rad_product(A,B,C)*R
                triple,g = normalize(A,B,C,x,y,z)
                assert triple == (a,b,c) and g == A*B*C//d
                record('abc_embeddings',(A,B,C,a,b,c,x,y,z,d))

    obstruction_witnesses=[]
    for n in range(1,33):
        A,B,C = 2**n,3**n,5**n
        x,y,z = 15**n,10**n,-2*6**n
        triple,g = normalize(A,B,C,x,y,z)
        assert math.gcd(x,y,z)==1 and g==30**n==math.lcm(A,B,C)
        assert triple == (1,1,2) and rad_product(A,B,C)==30 and rad_product(x,y,z)==30
        record('varying_base_obstructions',(n,g,*triple))
        if n<=5:
            obstruction_witnesses.append(dict(n=n,bases=[A,B,C],coefficients=[x,y,z],g=g,normalized=list(triple)))
    triple,g = normalize(2,3,5,15,10,-12)
    assert g == 30 and math.gcd(15,10,12) == 1
    record('sharp_gcd_witnesses',(2,3,5,15,10,-12,g))

    cert = {'case_digest_sha256':digest.hexdigest(),'counts':counts,
            'varying_base_witnesses':obstruction_witnesses,
            'domains':{'generic_gcd':{'bases':[1,8],'nonzero_coefficients':small},
                       'relations':{'bases':[1,9],'nonzero_x_y':[-12,12],'z':'determined by relation'},
                       'embedding':{'c_max':300,'a_le_b':True,'fixed_bases':fixed_bases},
                       'varying_base_n':[1,32]}}
    canonical=json.dumps(cert,sort_keys=True,separators=(',',':')).encode()
    result={'status':'CHECKED','passed':True,'problem':'ABC','resolution':'unknown',
            'agent':'wave2_agent4','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'certificate_sha256':hashlib.sha256(canonical).hexdigest(),'counts':counts,
            'python':platform.python_version(),'github_run_id':os.getenv('GITHUB_RUN_ID'),
            'source_commit':os.getenv('GITHUB_SHA'),
            'scope':'Exact bounded integer checks of the stated structural identities and conditional algebra; no infinite sequence or global abc estimate is established.',
            'closed_core_bottlenecks':0,'remaining_fixed_base_disproof_core_obligations':1}
    (out/'certificates.json').write_text(json.dumps(cert,indent=2)+'\n')
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
