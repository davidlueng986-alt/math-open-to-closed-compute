#!/usr/bin/env python3
"""Exact finite certificates and falsification tests for ABC Track 2.

The general proofs are in REPORT.md. This executable does NOT establish abc,
estimate any unspecified constant in a cited theorem, or prove an infinite
statement by finite search. It checks exact arithmetic consequences and witnesses.
"""
import hashlib
import json
import math
import os
import platform
import sys
from decimal import Decimal, localcontext
from pathlib import Path


def factor(n):
    assert n >= 1
    ans = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        ans[n] = ans.get(n, 0) + 1
    return ans


def stats(n):
    fs = factor(n)
    assert math.prod(p ** e for p, e in fs.items()) == n
    return {
        'factorization': fs,
        'rad': math.prod(fs),
        'largest_prime': max(fs, default=1),
        'exponent_product': math.prod(fs.values()),
        'cube_excess': math.prod(p ** max(e-3, 0) for p, e in fs.items()),
        'max_exponent': max(fs.values(), default=0),
    }


def main():
    shard, shards = map(int, sys.argv[1:3])
    out = Path(sys.argv[3]); out.mkdir(parents=True, exist_ok=True)
    assert 0 <= shard < shards
    # A deterministic exhaustive finite box, with exact divisibility/arithmetic.
    bound = 600
    data = [None] + [stats(n) for n in range(1, bound + 1)]
    counters = {'primitive_triples': 0, 'balanced_triples': 0,
                'balanced_fourth_power_free': 0, 'exponent_tail_checks': 0}
    for c in range(2 + shard, bound + 1, shards):
        for a in range(1, c // 2 + 1):
            b = c-a
            if math.gcd(a,b) != 1:
                continue
            sa,sb,sc = data[a],data[b],data[c]
            assert math.gcd(a,c) == math.gcd(b,c) == 1
            R = sa['rad']*sb['rad']*sc['rad']
            qmin = min(s['largest_prime'] for s in [sa,sb,sc])
            assert qmin**3 <= R
            exps = list(sa['factorization'].values()) + list(sb['factorization'].values()) + list(sc['factorization'].values())
            prod_e = math.prod(exps)
            for B in [2,3,4,8,16]:
                t = sum(e >= B for e in exps)
                assert B**t <= prod_e
                counters['exponent_tail_checks'] += 1
            counters['primitive_triples'] += 1
            if 4*a >= c:
                U = sa['cube_excess']*sb['cube_excess']*sc['cube_excess']
                assert a*b*c <= R**3*U
                assert 3*c**3 <= 16*a*b*c
                assert 3*c**3 <= 16*R**3*U
                counters['balanced_triples'] += 1
                if max(exps,default=0) <= 3:
                    assert U == 1
                    assert 3*c**3 <= 16*R**3
                    counters['balanced_fourth_power_free'] += 1

    # Explicit infinite-family obstruction is proved in the report;
    # here we certify its first 24 parameters exactly.
    family = []
    for m in range(2 + shard,25,shards):
        a,b,c = 2**m-1,2**m+1,2**(m+1)
        assert a+b == c and math.gcd(a,b) == 1 and 4*a >= c
        ss=[stats(a),stats(b),stats(c)]
        R=math.prod(s['rad'] for s in ss)
        U=math.prod(s['cube_excess'] for s in ss)
        assert R <= 2*a*b < 2**(2*m+1)
        assert U >= 2**(m-2)
        # Exact rational version of (U / R^(1/4))^4 > 2^(2m-9).
        assert U**4*512 > R*2**(2*m)
        family.append({'m':m,'a':a,'b':b,'c':c,'R':R,'cube_excess':U,
                       'violates_U_le_R_quarter':U**4>R})

    # Product-of-valuations control does not control weighted valuation mass
    # for arbitrary integers. These are expressly NOT abc triples.
    model=[]
    for p in [101,1009,10007,100003,1000003]:
        assert factor(p)=={p:1}
        R=2*p;e=math.isqrt(R)
        assert e*e<=R
        model.append({'prime':p,'radical':R,'exponents':[e,1],
                      'product_of_exponents':e,
                      'logM_over_logR':(e*math.log(2)+math.log(p))/math.log(R),
                      'scope':'factorization model, not an additive triple'})

    # Reproduce the smooth n^2+1 example cited by Cuevas Barrientos--Pasten.
    n=24208144
    smooth=stats(n*n+1)
    assert smooth['largest_prime']==89
    assert math.gcd(n*n,n*n+1)==1

    # Diagnostic values illustrate a proved asymptotic comparison; they do
    # not stand in for the proof or use an inferred theorem constant.
    with localcontext() as ctx:
        ctx.prec=60
        envelope=[]
        for raw in [100,1000,10000,1000000]:
            L=Decimal(raw); logL=L.ln()
            t=(L*logL).sqrt()
            envelope.append({'log_R':raw,
                'illustrative_kappa':1,
                'log_Pasten_envelope_over_abc_log_scale':str(t-logL),
                'log_Pasten_trivial_q_envelope_over_SY':str(t-3*logL)})

    result={'task':'abc-wave1-agent2-bounds','status':'CHECKED',
      'proof_scope':'finite exact checks of structural lemmas and explicit obstruction family; no abc closure',
      'shard':shard,'shards':shards,'c_bound':bound,'counts':counters,
      'failed_auxiliary_claim':'cube_excess <= K_delta * R^delta for every balanced abc triple and every delta>0',
      'counterexample_family':family,
      'factorization_only_models':model,
      'n2plus1_example':{'n':n,**smooth},
      'envelope_diagnostics':envelope,
      'python':platform.python_version(),
      'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'github_run_id':os.getenv('GITHUB_RUN_ID'),
      'github_sha':os.getenv('GITHUB_SHA')}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'counts':counters,
      'family_certificates':len(family),'n2plus1_largest_prime':89,
      'source_sha256':result['source_sha256']},sort_keys=True))


if __name__=='__main__':
    main()
