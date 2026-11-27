#!/usr/bin/env python3
"""Exact finite audit of the height budget; no infinite estimate is inferred."""
import argparse
import hashlib
import itertools
import json
import math
import os
import platform
from fractions import Fraction
from pathlib import Path

def factor(n):
    assert n >= 1
    f = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def invariants(a1,a2,a3,a4,a6):
    b2=a1*a1+4*a2
    b4=2*a4+a1*a3
    b6=a3*a3+4*a6
    b8=a1*a1*a6+4*a2*a6-a1*a3*a4+a2*a3*a3-a4*a4
    c4=b2*b2-24*b4
    c6=-b2**3+36*b2*b4-216*b6
    delta=-b2*b2*b8-8*b4**3-27*b6*b6+9*b2*b4*b6
    assert c4**3-c6*c6 == 1728*delta
    return c4,c6,delta

def budget(delta,c4,c6):
    d=abs(delta); assert d>0
    fs=factor(d); n=math.prod(fs)
    v=math.prod(p**max(e-6,0) for p,e in fs.items())
    s=math.prod(p**max(6-e,0) for p,e in fs.items())
    j=Fraction(c4**3,delta); bigj=max(abs(j),abs(j-1728))
    h=max(abs(c4)**3,c6*c6)
    assert bigj >= 864
    assert h == d*bigj
    assert d*s == n**6*v
    assert Fraction(h,n**6) == bigj*v/s
    return fs,n,h,j,bigj

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('shard',type=int)
    parser.add_argument('shards',type=int)
    parser.add_argument('outdir')
    parser.add_argument('--require-sage',action='store_true')
    args=parser.parse_args()
    assert (args.shard,args.shards)==(0,1), 'indivisible audit'
    out=Path(args.outdir);out.mkdir(parents=True,exist_ok=True)
    try:
        from sage.all import EllipticCurve
        from sage.env import SAGE_VERSION
        have_sage=True
    except ImportError:
        have_sage=False;SAGE_VERSION=None
    if args.require_sage and not have_sage:
        raise RuntimeError('Hosted geometric audit requires Sage')
    counts=dict(general_weierstrass_models=0,nonzero_discriminant_models=0,
                signed_budget_identities=0,semistable_criterion_models=0,
                factor_vector_budgets=0,restricted_budget_cases=0,
                low_j_family=0,sage_minimal_conductor_cases=0,
                exact_regime_compositions=0,reverse_half_epsilon_cases=0,
                unbounded_local_multiplicity_instances=0)
    digest=hashlib.sha256()
    for coeff in itertools.product([0,1],range(-2,3),[0,1],range(-8,9),range(-8,9)):
        counts['general_weierstrass_models']+=1
        c4,c6,delta=invariants(*coeff)
        if not delta: continue
        counts['nonzero_discriminant_models']+=1
        fs,n,h,j,bigj=budget(delta,c4,c6)
        counts['signed_budget_identities']+=1
        if math.gcd(c4,delta)==1:
            counts['semistable_criterion_models']+=1
        digest.update(json.dumps([coeff,c4,c6,delta,n,str(bigj)],separators=(',',':')).encode()+b'\n')
    for es in itertools.product(range(1,10),repeat=3):
        fs=dict(zip([2,3,5],es));d=math.prod(p**e for p,e in fs.items());n=30
        v=math.prod(p**max(e-6,0) for p,e in fs.items())
        s=math.prod(p**max(6-e,0) for p,e in fs.items())
        assert d*s==n**6*v
        counts['factor_vector_budgets']+=1
        for k in range(1,7):
            if max(es)<=k:
                for bigj in [Fraction(1,2)*n**(6-k),Fraction(7,3)*n**(6-k)]:
                    assert d*bigj <= Fraction(7,3)*n**6
                    counts['restricted_budget_cases']+=1
    rows=[]
    last_d=0
    for m in range(1,129):
        b=47*m
        c4,c6,delta=invariants(1,0,0,1,b)
        assert (c4,c6,delta)==(-47,71-864*b,-432*b*b+71*b-63)
        assert math.gcd(c4,delta)==1
        fs,n,h,j,bigj=budget(delta,c4,c6)
        assert 0<j<245 and bigj<1728 and h==(864*b-71)**2
        assert abs(delta)>last_d
        last_d=abs(delta)
        row=dict(m=m,B=b,c4=c4,c6=c6,delta=delta,factorization={str(p):e for p,e in fs.items()},predicted_conductor=n,H=h,j=str(j),J=str(bigj))
        if have_sage and m<=32:
            curve=EllipticCurve([1,0,0,1,b])
            minimal=curve.global_minimal_model()
            assert tuple(map(int,curve.c_invariants()))==(c4,c6)
            assert tuple(map(int,minimal.c_invariants()))==(c4,c6)
            assert int(minimal.discriminant())==delta
            assert int(curve.conductor())==n
            assert curve.conductor().is_squarefree()
            row['sage_conductor']=int(curve.conductor())
            row['sage_minimal_discriminant']=int(minimal.discriminant())
            counts['sage_minimal_conductor_cases']+=1
        rows.append(row);counts['low_j_family']+=1
    # N=t^s, eta=2/s: eta/2 and eta powers are exact integers t and t^2.
    for s,t,A,B in itertools.product(range(1,9),range(2,10),[Fraction(1),Fraction(3,2)],[Fraction(1),Fraction(5,3)]):
        n=t**s
        for q in [Fraction(1,2),Fraction(1),Fraction(3,2),Fraction(2)]:
            bigj=1728*t*q
            if bigj<=1728*t:
                for scale in [Fraction(1,2),Fraction(1)]:
                    d=A*n**6*t*scale
                    assert d*bigj<=max(1728*A,B)*n**6*t*t
                    counts['exact_regime_compositions']+=1
            else:
                for scale in [Fraction(1,2),Fraction(1)]:
                    d=B*n**6*t*t/bigj*scale
                    assert d*bigj<=max(1728*A,B)*n**6*t*t
                    counts['exact_regime_compositions']+=1
            d=A*n**6*t/bigj
            assert d <= A/864*n**6*t
            counts['reverse_half_epsilon_cases']+=1
    for k in range(5,33):
        b=2**k
        delta=b*b*(b-1)**2//256
        e=0;tmp=delta
        while tmp%2==0: e+=1;tmp//=2
        assert e==2*k-8
        counts['unbounded_local_multiplicity_instances']+=1
    certificate={'general_models_digest_sha256':digest.hexdigest(),'low_j_family':rows,
                 'counts':counts,'scope':'Exact finite identities and tests; synthetic rational budgets are not asserted to be elliptic curves.'}
    canonical=json.dumps(certificate,sort_keys=True,separators=(',',':')).encode()
    (out/'certificates.json').write_text(json.dumps(certificate,indent=2)+'\n')
    result={'status':'CHECKED','problem':'ABC','original_resolution':'unknown','agent':'wave2_agent5',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'certificate_sha256':hashlib.sha256(canonical).hexdigest(),'counts':counts,
            'python_version':platform.python_version(),'sage_available':have_sage,'sage_version':SAGE_VERSION,
            'sage_required':args.require_sage,'run_id':os.environ.get('GITHUB_RUN_ID'),
            'source_commit':os.environ.get('GITHUB_SHA'),'domain':{'general_coefficients':{'a1':[0,1],'a2':[-2,2],'a3':[0,1],'a4':[-8,8],'a6':[-8,8]},'low_j_family_m':[1,128],'sage_m':[1,32] if have_sage else []},
            'limitations':['Finite checks do not prove either open height estimate.','The local reduction criterion is a classical import.','No Lean verification claimed.']}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
