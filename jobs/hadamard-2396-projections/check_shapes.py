"""Independently reconstruct the invariant 133-point shapes using scalar correlation sums."""
import itertools, math
from collections import defaultdict
from functools import cache
def orb(x,q):
    if x%q==0:return 0
    return 1 if x%q in {j*j%q for j in range(q)} else 2
@cache
def primes(q):
    h=(q-1)//2;m=1197//q;total=2396-2*m
    vals=range(-math.isqrt(total)|1,math.isqrt(total)+1,2)
    by=defaultdict(list)
    for a,b in itertools.product(vals,repeat=2):
        r=1-h*(a+b);norm=r*r+h*(a*a+b*b)
        if norm<total:by[norm].append((r,a,b))
    return [(x,y) for n,ls in by.items() for x in ls if x[1]>=x[2]
            for y in by.get(total-n,())]
@cache
def triples(v):
    opt=range(-9,10,2)
    return [z for z in itertools.product(opt,repeat=3) if z[0]+9*(z[1]+z[2])==v]
cl=[3*orb(j,7)+orb(j,19) for j in range(133)]
pairs=defaultdict(lambda:defaultdict(int))
for s in (0,1,2,7,19):
    for i in range(133):pairs[s][cl[i],cl[(i+s)%133]]+=1
@cache
def blocks(seven,nineteen):
    out=defaultdict(list)
    for x,y,z in itertools.product(*map(triples,seven)):
        if tuple(x[i]+3*(y[i]+z[i]) for i in range(3))!=nineteen:continue
        row=x+y+z
        key=tuple(sum(n*row[i]*row[j] for (i,j),n in p.items()) for p in pairs.values())
        if key[0]<=2378:out[key].append(row)
    return out
def main():
    result=set()
    for a,b in primes(7):
        for c,d in primes(19):
            A,B=blocks(a,c),blocks(b,d)
            for key,ls in A.items():
                goal=tuple(t-x for t,x in zip((2378,-18,-18,-18,-18),key))
                result.update(itertools.product(ls,B.get(goal,())))
    return sorted(result)
if __name__=='__main__':
    from shapes import shapes
    direct, gauss = main(), shapes()
    if direct != gauss:
        raise ValueError("scalar orbit sums and Gauss sums found different shapes")
    print(f"{len(direct)} normalized 133-point shapes, identical by both enumerations")
