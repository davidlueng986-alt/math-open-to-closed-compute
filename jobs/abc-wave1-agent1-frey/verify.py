#!/usr/bin/env python3
"""Exact symbolic and finite checks for the ABC/Frey reduction.

Finite checks do not prove abc or the imported local reduction theorem.
If Sage is available, independently check minimal models and conductors.
"""
import json
import math
import os
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

try:
    from sage.all import EllipticCurve, QQ
    HAVE_SAGE = True
except ImportError:
    HAVE_SAGE = False


def radical(n):
    assert n
    return math.prod(map(int, sp.factorint(abs(n))))


def valuation2(n):
    n = abs(n)
    assert n
    result = 0
    while n % 2 == 0:
        n //= 2
        result += 1
    return result


def invariants(a1, a2, a3, a4, a6):
    b2 = a1*a1 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3*a3 + 4*a6
    b8 = a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4
    c4 = b2*b2 - 24*b4
    c6 = -b2**3 + 36*b2*b4 - 216*b6
    disc = -b2*b2*b8 - 8*b4**3 - 27*b6*b6 + 9*b2*b4*b6
    return tuple(sp.expand(z) for z in (c4, c6, disc))


def normalize(a, b, c):
    if b % 2 == 0:
        return a, b, c
    if a % 2 == 0:
        return b, a, c
    return -a, c, b


def transform(u, v, w):
    assert u + v == w and u % 2 and not v % 2
    return (u-v)**2, 4*u*v, w*w


def symbolic_checks():
    a, b = sp.symbols('a b')
    c4, c6, disc = invariants(0, b-a, 0, -a*b, 0)
    assert sp.expand(c4 - 16*(a*a+a*b+b*b)) == 0
    assert sp.expand(c6 - 32*(a-b)*(2*a+b)*(a+2*b)) == 0
    assert sp.expand(disc - 16*a*a*b*b*(a+b)**2) == 0
    assert sp.expand(c4**3-c6**2-1728*disc) == 0
    nc4, nc6, nd = invariants(1, (b-a-1)/4, 0, -a*b/16, 0)
    assert sp.expand(nc4 - c4/16) == 0
    assert sp.expand(nc6 - c6/64) == 0
    assert sp.expand(nd - disc/4096) == 0
    assert sp.expand((a-b)**2+4*a*b-(a+b)**2) == 0
    return 8


def run(shard, shards, outdir):
    symbolic_count = symbolic_checks()
    max_c = int(os.environ.get('ABC_AGENT1_MAX_C', '60'))
    cases = sage_cases = odd_odd = 0
    samples = []
    index = 0
    for c in range(2, max_c+1):
        for a in range(1, c):
            b = c-a
            if math.gcd(a, b) != 1:
                continue
            index += 1
            if (index-1) % shards != shard:
                continue
            r = radical(a*b*c)
            t = normalize(a,b,c)
            m = max(map(abs,t))
            assert m == c and radical(math.prod(t)) == r
            assert t[0] % 2 and not t[1] % 2
            old = t
            for _ in range(2):
                new = transform(*old)
                old_m, new_m = max(map(abs,old)), max(map(abs,new))
                old_r = radical(math.prod(old))
                new_r = radical(math.prod(new))
                assert new[0]+new[1] == new[2]
                assert math.gcd(new[0],new[1]) == 1
                assert old_m**2 <= new_m <= 4*old_m**2
                assert new_r == old_r*radical(old[0]-old[1])
                assert new_r <= 2*old_m*old_r
                assert valuation2(new[1]) == valuation2(old[1])+2
                old = new
            A,B,C = [-z for z in old]
            M = max(abs(A),abs(B),abs(C))
            R = radical(A*B*C)
            assert M >= c**4
            assert R <= 16*c**3*r
            assert A % 4 == 3 and B % 32 == 0
            ai = [1, (B-A-1)//4, 0, -A*B//16, 0]
            c4,c6,disc = map(int,invariants(*ai))
            assert disc == (A*B*C)**2//256
            assert c4 == A*A+A*B+B*B
            assert math.gcd(c4,disc) == 1
            assert 2*c4 >= M*M
            H = max(abs(c4)**3,c6*c6)
            assert 8*H >= c**24
            g = math.gcd(abs(c4)**3,c6*c6)
            assert 1728 % g == 0
            if HAVE_SAGE and sage_cases < 240:
                E = EllipticCurve(QQ,ai)
                assert int(E.discriminant()) == disc
                assert abs(int(E.global_minimal_model().discriminant())) == abs(disc)
                assert int(E.conductor()) == R
                assert E.conductor().is_squarefree()
                sage_cases += 1
            cases += 1
            odd_odd += bool(a%2 and b%2)
            if len(samples) < 5:
                samples.append({'abc':[a,b,c],'signed_frey':[A,B,C],
                                'radical':R,'predicted_conductor':R,
                                'minimal_discriminant':disc})
    exponents = []
    for eta in [Fraction(1,100),Fraction(1,10),Fraction(1),Fraction(3)]:
        delta = eta/(36+5*eta)
        assert 6*(1+delta)/(1-5*delta) == 6+eta
        theta = eta/(4+3*eta)
        assert (1+theta)/(1-3*theta) == 1+eta
        exponents.append({'epsilon':str(eta),'abc_to_ms_delta':str(delta),
                          'ms_to_abc_theta':str(theta)})
    arch_samples=[]
    for n in range(5,25):
        b = 2**n
        c4 = b*b-b+1
        disc = b*b*(b-1)**2//256
        j = Fraction(c4**3,disc)
        N = 2*radical(b-1)
        assert j >= 32*b*b
        assert N <= 2*b
        assert j >= 8*N*N
        if HAVE_SAGE:
            E=EllipticCurve(QQ,[1,b//4,0,b//16,0])
            assert int(E.conductor()) == N
            assert int(E.discriminant()) == disc
        arch_samples.append({'n':n,'N':N,'j_ge_8_N_squared':True})
    result={'status':'CHECKED','claim_scope':'symbolic identities and stated finite sample only',
            'abc_status':'BLOCKED','max_c':max_c,'shard':shard,'shards':shards,
            'coprime_triples_checked':cases,'both_odd_inputs_checked':odd_odd,
            'symbolic_identities_checked':symbolic_count,
            'sage_available':HAVE_SAGE,'sage_minimal_conductor_cases':sage_cases,
            'semistable_model_family_samples':samples,
            'epsilon_conversions':exponents,'archimedean_obstruction_samples':arch_samples,
            'limitations':['Finite testing does not prove a conductor theorem or abc.',
                           'Universal elementary proofs are in REPORT.md.',
                           'Sage conductor checks are skipped, explicitly, if Sage is unavailable.']}
    outdir=Path(outdir);outdir.mkdir(parents=True,exist_ok=True)
    (outdir/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','max_c','coprime_triples_checked','both_odd_inputs_checked','sage_available','sage_minimal_conductor_cases']},indent=2))


if __name__=='__main__':
    run(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3])
