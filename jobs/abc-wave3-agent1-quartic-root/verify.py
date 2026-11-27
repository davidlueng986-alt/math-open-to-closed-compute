#!/usr/bin/env python3
"""Exact finite implementation checks for the quartic root reduction.
The infinite nonsquareness and implication are written proofs, not inferred here.
"""
from __future__ import annotations
import argparse, hashlib, json, math
from fractions import Fraction
from pathlib import Path


def factor(n: int) -> dict[int,int]:
    assert n > 0
    fs={}
    p=2
    while p*p<=n:
        while n%p==0:
            fs[p]=fs.get(p,0)+1;n//=p
        p=3 if p==2 else p+2
    if n>1: fs[n]=fs.get(n,0)+1
    return fs


def rad(n: int) -> int:
    return math.prod(factor(n))


def sq(n: int) -> bool:
    return n>=0 and math.isqrt(n)**2==n


def mapped(a: int,b: int,c: int) -> tuple[int,int,int]:
    assert a+b==c and a>0 and b>0 and c%2==1 and b%2==0
    return c**4-b**4,b**4,c**4


def main() -> None:
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=240)
    ap.add_argument('--out',type=Path,default=Path('local-evidence'))
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    counts={'odd_primitive_triples':0,'independent_output_factorizations':0,'even_parity_transports':0,'epsilon_identities':0,'triangle_identities':0,'product_cusp_lower_bounds':0}
    examples=[]
    for c in range(3,args.limit+1,2):
        for b in range(2,c,2):
            a=c-b
            if math.gcd(a,b)!=1:continue
            A,B,C=mapped(a,b,c)
            P,Q=c+b,c*c+b*b
            assert A>0 and A+B==C and math.gcd(A,B)==1
            assert C%2==1 and A%2==1 and B%2==0
            assert sq(C) and not sq(A)
            assert A==a*P*Q
            assert math.gcd(P,Q)==math.gcd(P,a*b*c)==math.gcd(Q,a*b*c)==1
            R=rad(a)*rad(b)*rad(c)
            Rp=R*rad(P)*rad(Q)
            assert Rp<=R*P*Q<4*R*c**3
            counts['odd_primitive_triples']+=1
            if c<=70:
                assert Rp==rad(A)*rad(B)*rad(C)
                counts['independent_output_factorizations']+=1
            X,Y,Z=2*b*b*c*c,c**4-b**4,c**4+b**4
            assert X*X+Y*Y==Z*Z
            assert X*Y==2*(b*c)**2*(c**4-b**4)
            counts['triangle_identities']+=1
            if 2*b>=c:
                assert 128*A*B*C>=15*a*c**11
                counts['product_cusp_lower_bounds']+=1
            if len(examples)<12 or (a==1 and c in (81,125,225)):
                examples.append({'input':[a,b,c],'output':[A,B,C],'input_radical':R,'output_radical':Rp,'new_factors':[P,Q],'root_certificate':{'height_square':c*c,'odd_leg_isqrt':math.isqrt(A),'odd_leg_nonsquare':True}})
    for c in range(2,min(args.limit,100)+1,2):
        for a in range(1,c,2):
            b=c-a
            if math.gcd(a,b)!=1:continue
            ell=a+c
            aa,bb,cc=b*b,4*a*c,ell*ell
            assert aa+bb==cc and math.gcd(aa,bb)==1 and cc%2==1
            assert math.gcd(ell,a*b*c)==1
            R=rad(a)*rad(b)*rad(c)
            Rodd=rad(aa)*rad(bb)*rad(cc)
            assert Rodd==R*rad(ell)
            A,B,C=mapped(aa,bb,cc)
            assert A+B==C and math.gcd(A,B)==1 and C==ell**8
            assert sq(C) and not sq(A)
            P,Q=cc+bb,cc*cc+bb*bb
            # The radical is certified by factors, not by trusting the upper bound.
            all_primes=set(factor(aa))|set(factor(bb))|set(factor(cc))|set(factor(P))|set(factor(Q))
            Rp=math.prod(all_primes)
            assert Rp<=4*Rodd*cc**3<=4*R*ell**7
            counts['even_parity_transports']+=1
    for p in range(1,51):
        for q in (1,2,7,31):
            eps=Fraction(p,q)
            delta=eps/(8*(1+eps));eta=eps/(4+3*eps)
            assert 0<delta<Fraction(1,8)<Fraction(1,2)
            assert 1-8*delta==1/(1+eps)
            assert 0<eta<Fraction(1,3)
            assert (1+eta)/(1-3*eta)==1+eps
            assert 1-4*delta>=1-8*delta
            counts['epsilon_identities']+=1
    result={'status':'CHECKED','scope':'Exact finite implementation checks only; not proof of ROOT or full abc.','limit':args.limit,'counts':counts,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'original_abc_closed':False,'new_global_core_estimates_proved':0,'root_core_premise':'W2-A2-ROOT-BOUND','root_core_premise_status':'BLOCKED'}
    (args.out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    (args.out/'certificates.json').write_text(json.dumps(examples,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
