"""Enumerate normalized 133-point layers invariant under quadratic residues at both primes."""
import itertools
import math
import sys
from collections import defaultdict
from functools import cache


def prime_parameters(q):
    # A quadratic-residue-constant row has two odd orbit values b+c,b-c and sum one.
    bound = math.isqrt(2396)
    by_energy = defaultdict(list)
    for b in range(-bound, bound+1):
        for c in range(-bound, bound+1):
            energy = (1-q*b)**2+q*c*c
            if (b+c) % 2 and energy <= 2396:
                by_energy[energy].append((b,c))
    # A simultaneous nonsquare multiplier can orient the first row at each prime.
    return [(x,y) for n, left in by_energy.items() for x in left if x[1] >= 0
            for y in by_energy.get(2396-n,())]


@cache
def block_rows(parameter):
    b, c = parameter
    seven = (1-6*b, b+c, b-c)
    options = []
    for value in seven:
        options.append([(u,v) for u in range(-9,10) if abs(value-18*u) <= 9
                        for v in range(-9,10) if (u+v) % 2 and abs(u)+abs(v) <= 9])
    rows = defaultdict(lambda: defaultdict(list))
    for params in itertools.product(*options):
        u,v = zip(*params)
        b19, c19 = u[0]+3*(u[1]+u[2]), v[0]+3*(v[1]+v[2])
        if (1-19*b19)**2+19*c19*c19 > 2396:
            continue
        d = [x-19*y for x,y in zip(seven,u)]
        a,b = 2*d[0]-d[1]-d[2], d[1]-d[2]
        e,f = 2*v[0]-v[1]-v[2], v[1]-v[2]
        energy = a*a+7*b*b+19*(e*e+7*f*f)
        if energy <= 4*2396:
            cells = tuple(x for m,(s,t) in zip(seven,params) for x in (m-18*s,s+t,s-t))
            rows[b19,c19][energy,a*f-b*e].append(cells)
    return rows


def orbit(i, q):
    return 0 if i%q == 0 else (1 if pow(i%q,(q-1)//2,q)==1 else 2)


def shapes():
    pairs = set()
    for u,v in prime_parameters(7):
        left, right = block_rows(u), block_rows(v)
        for x,y in prime_parameters(19):
            for (energy,det), a in left.get(x,{}).items():
                b = right.get(y,{}).get((4*2396-energy,-det), ())
                pairs.update(itertools.product(a,b))
    ordered = sorted(pairs)
    for pair in ordered:
        rows = [[r[3*orbit(i,7)+orbit(i,19)] for i in range(133)] for r in pair]
        assert [sum(r) for r in rows] == [1,1]
        for s in range(133):
            assert sum(v*r[(i+s)%133] for r in rows for i,v in enumerate(r)) == (2378 if s==0 else -18)
    return ordered


if __name__ == "__main__":
    rows = shapes()
    if len(sys.argv) == 1:
        print(len(rows))
    else:
        for row in rows[int(sys.argv[1])]:
            print(*row)
