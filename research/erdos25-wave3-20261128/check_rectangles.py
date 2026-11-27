#!/usr/bin/env python3
"""Finite regression checks for the rectangle localization proof, not a proof of Erdős #25."""
from fractions import Fraction
from itertools import product
from math import prod
import random

def model(primes, exponents):
    sizes=[p**e for p,e in zip(primes,exponents)]
    pts=list(product(*(range(n) for n in sizes)))
    N=len(pts)
    rectangles=[]
    for levels in product(*(range(e+1) for e in exponents)):
        mods=[p**l for p,l in zip(primes,levels)]
        for digits in product(*(range(m) for m in mods)):
            rectangles.append(sum(1<<i for i,x in enumerate(pts)
                                  if all(a%m==b for a,m,b in zip(x,mods,digits))))
    fibers=[]
    for j,(p,e) in enumerate(zip(primes,exponents)):
        balls=[]
        for l in range(e+1):
            groups={}
            for i,x in enumerate(pts):
                key=x[:j]+(x[j]%(p**l),)+x[j+1:]
                groups[key]=groups.get(key,0)|(1<<i)
            balls.extend(groups.values())
        fibers.append(balls)
    return N,rectangles,fibers

def check(N,rectangles,fibers,S,eta):
    k=len(fibers)
    # Check directly the low-average rectangle union inequality.
    low=0
    for R in rectangles:
        if (S&R).bit_count()*eta.denominator < R.bit_count()*eta.numerator:
            low |= R
    loss=(low&S).bit_count()
    assert loss**k*eta.denominator <= (k*N)**k*eta.numerator
    # Verify the proof's intermediate pruning at an exact rational t, eta=t^k.
    t=next((Fraction(j,16) for j in range(1,17) if Fraction(j,16)**k>=eta),Fraction(1))
    G=S
    for balls in fibers:
        bad=0
        for B in balls:
            if (G&B).bit_count()*t.denominator < B.bit_count()*t.numerator:
                bad |= B
        new=G & ~bad
        assert (G^new).bit_count()*t.denominator <= N*t.numerator
        G=new
    for R in rectangles:
        if R&G:
            assert (S&R).bit_count()*t.denominator**k >= R.bit_count()*t.numerator**k

def main():
    rng=random.Random(20261128)
    count=0
    for primes,exponents,exhaustive in [([2,3],[2,1],True),([2,3,5],[1,1,1],False),([2,3,5],[2,1,1],False)]:
        N,rectangles,fibers=model(primes,exponents)
        masks=range(1<<N) if exhaustive else [rng.getrandbits(N) for _ in range(3000)]
        for S in masks:
            for eta in [Fraction(1,64),Fraction(1,16),Fraction(1,8),Fraction(1,4),Fraction(1,2)]:
                check(N,rectangles,fibers,S,eta)
                count+=1
        print(f"PASS primes={primes}, exponents={exponents}, points={N}, rectangles={len(rectangles)}",flush=True)
    print(f"PASS {count} mask/threshold checks; finite regression only",flush=True)

if __name__=="__main__":
    main()
