#!/usr/bin/env python3
"""Independent verifier: standard library, exact integers and trial division."""
import argparse
import functools
import json
import math
from pathlib import Path

@functools.lru_cache(maxsize=None)
def is_prime(n):
    if n<2:return False
    if n in (2,3):return True
    if n%2==0 or n%3==0:return False
    d=5
    while d*d<=n:
        if n%d==0 or n%(d+2)==0:return False
        d+=6
    return True

def check(c):
    a,b,z=map(lambda k:int(c[k]),('a','b','c'))
    assert 0<a<=b and a+b==z and math.gcd(a,b)==math.gcd(a,z)==math.gcd(b,z)==1
    ps=set()
    for n,fac in zip((a,b,z),c['factors']):
        pairs=[(int(p),int(e)) for p,e in fac]
        assert len({p for p,e in pairs})==len(pairs)
        assert all(is_prime(p) and e>0 for p,e in pairs)
        assert math.prod(p**e for p,e in pairs)==n
        ps.update(p for p,e in pairs)
    R=math.prod(ps)
    assert R==int(c['radical'])
    assert (z**5>R**8)==c['quality_gt_8_over_5']
    origin=c.get('origin',{})
    if 'bases' in origin:
        terms=[int(x)*int(y) for x,y in zip(origin['bases'],origin['coefficients'])]
        assert sum(terms)==0 and 0 not in terms
        g=math.gcd(*terms)
        assert sorted(abs(t)//g for t in terms)==sorted((a,b,z))
    return a,b,z,R

def check_bracket(c,R,b):
    n=b['epsilon_numerator'];d=b['epsilon_denominator'];s=b['denominator']
    lo=int(b['lower_numerator']);hi=int(b['upper_numerator'])
    assert n>0 and d>0 and s>0 and 0<=lo<hi
    assert (c*s)**d>lo**d*R**(d+n)
    assert (c*s)**d<hi**d*R**(d+n)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('file');ap.add_argument('--output');args=ap.parse_args()
    data=json.loads(Path(args.file).read_text());ref=check(data['reference'])
    known=(2,6436341,6436343,15042)
    assert ref==known
    for b in data['record_constant_brackets']:check_bracket(ref[2],ref[3],b)
    certs={}
    for cert in data.get('candidates',[]):
        a,b,c,R=check(cert);certs[(a,b,c)]=R
    for r in data.get('finite_search_constant_witnesses',[]):
        t=tuple(map(int,r['source_triple']));check_bracket(t[2],certs[t],r['bracket'])
    result=dict(status='CHECKED',scope='Listed finite integer/factorization/quality/constant certificates only',reference=list(known),candidate_certificates=len(certs),prime_tests=is_prime.cache_info().currsize,record_constant_brackets=len(data['record_constant_brackets']),passed=True)
    if args.output:Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
