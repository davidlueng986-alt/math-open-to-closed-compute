"""Integer PAF checks for the cyclic and elementary-3 abelian groups of order 1197."""

from functools import cache
from itertools import product
from math import gcd
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"hadamard-2396-projections"))
from verify import LENGTH, original, paf, words

N=LENGTH
MASK=(1<<N)-1
TRITS=[sum(1<<i for i in range(a,N,3)) for a in range(3)]
COORDS=[((i%9)//3,i%3,i%133) for i in range(N)]
INDEX={v:i for i,v in enumerate(COORDS)}


def minus(i,plane):
    if not plane:
        return -i%N
    a,b,c=COORDS[i]
    return INDEX[-a%3,-b%3,-c%133]


def rotate(word, shift):
    s=shift%N
    return (word>>s)|((word<<(N-s))&MASK)


def all_paf(masks, plane, scalar):
    signs=words(masks)
    if [sum(r) for r in signs] != [1,1]:
        raise ValueError("incorrect row weights")
    numbers=[int(m,16) for m in masks]
    labels=[s for s in range(1,N) if s < minus(s,plane)]
    if not plane:
        values=original(masks)
    else:
        values=[]
        for s in labels:
            carry=sum(TRITS[h] for h in range(3) if h+s%3>=3)
            d=0
            for b in numbers:
                rotated=(rotate(b,s)&(MASK^carry))|(rotate(b,s-399)&carry)
                d+=(b^rotated).bit_count()
            values.append(2*N-2*d)
    if scalar:
        for s,want in zip(labels,values):
            if plane:
                x,y,t=COORDS[s]
                perm=[INDEX[(a+x)%3,(b+y)%3,(c+t)%133] for a,b,c in COORDS]
                got=sum(row[i]*row[j] for row in signs for i,j in enumerate(perm))
            else:
                got=paf(signs,s)
            if got!=want:raise ValueError(f"scalar and rotated correlations disagree at {s}")
    return dict(zip(labels,values))


def audit(masks, law, group, scalar=True):
    if law not in ("cyclic","plane"):
        raise ValueError("unknown group law")
    plane=law=="plane"
    group=set(group)
    if 1 not in group or any(gcd(x,N)!=1 or x%3!=1 or not 0<x<N for x in group):
        raise ValueError("invalid multipliers")
    if {x*y%N for x in group for y in group} != group:
        raise ValueError("multipliers not closed")
    rows=words(masks)
    if any(row[x]!=row[x*g%N] for row in rows for x in range(N) for g in group):
        raise ValueError("signs break the advertised group")
    values=all_paf(masks,plane,scalar)
    def canon(s):
        return min(min(s*g%N,minus(s*g%N,plane)) for g in group)
    classes={canon(i) for i in values}
    if any(values[canon(i)]!=value for i,value in values.items()):
        raise ValueError("correlations break the group")
    quotient={}
    for q in (57,63,133,399):
        T=[[sum(row[j::q]) for j in range(q)] for row in rows]
        def add(x,y):
            if q==63 and plane:
                return (x+y-21*(x%3+y%3>=3))%q
            return (x+y)%q
        C=[sum(row[i]*row[add(i,t)] for row in T for i in range(q)) for t in range(q)]
        e=[v-(2396-2*(N//q) if t==0 else -2*(N//q)) for t,v in enumerate(C)]
        quotient[str(q)]=(sum(v*v for v in e)+e[0]*e[0])//2
    return {"raw_energy":sum((v+2)**2 for v in values.values()),"raw_exact_pairs":sum(v==-2 for v in values.values()),
            "raw_peak_error":max(abs(v+2) for v in values.values()),"raw_paf_at_one":values[1],
            "raw_paf_at_399":values[399],"quotient_energies":quotient,"lag_classes":len(classes),
            "word_orbits":len({min(i*g%N for g in group) for i in range(N)})}


@cache
def groups(size):
    squares={p:{j*j%p for j in range(1,p)} for p in (3,7,19)}
    allowed={j for j in range(1,N) if gcd(j,N)==1 and all(j%p in s for p,s in squares.items())}
    cyclic={}
    for g in allowed:
        s={1};h=g
        while h not in s:s.add(h);h=h*g%N
        cyclic[g]=s
    start=frozenset([1]);seen={start};stack=[start]
    while stack:
        current=stack.pop()
        for a in allowed-current:
            made=frozenset(i*j%N for i,j in product(current,cyclic[a]))
            if len(made)>9 or 400 in made or made in seen:continue
            seen.add(made);stack.append(made)
    result=sorted(tuple(sorted(s)) for s in seen if len(s)==size)
    if len(result)!={1:1,3:12,9:18}[size]:raise ValueError("wrong multiplier census")
    return result
