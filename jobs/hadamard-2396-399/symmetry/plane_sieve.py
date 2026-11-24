"""Test the pure square action on C3 x C3 x C7 x C19 using its actual quotients."""

from collections import Counter
from functools import cache
from itertools import product
from pathlib import Path
import subprocess
import sys
from sieve import orientation_ok, canonical

POINT = [(i%9//3,i%3,i%7) for i in range(63)]
INDEX = {p:i for i,p in enumerate(POINT)}


@cache
def plane_canonical(v):
    return min(tuple(v[3*((a+s*x)%3)+(b+s*y)%3] for x in range(3) for y in range(3))
               for a,b,s in product(range(3),range(3),(1,-1)))


def characterize(templates,binary):
    lines=[tuple(map(int,s.split())) for s in templates.read_text().splitlines()]
    orientations={}
    for i,(w,a,x,b,y,h) in enumerate(lines):
        za,zb=w-2*x.bit_count(),7-w-2*y.bit_count()
        for sa,sb in product((1,-1),repeat=2):
            if orientation_ok(sa*za,sb*zb,w): orientations[i,sa,sb]=(a,x,b,y)
    accepted=set(orientations)
    maps=[(f"3({u},{v})",3,[(u*a+v*b)%3 for a,b,_ in POINT]) for u,v in ((1,0),(0,1),(1,1),(1,2))]
    maps += [("7",7,[c for _,_,c in POINT]),("3x3",-9,[3*a+b for a,b,_ in POINT])]
    for name,q,projection in maps:
        rows,pairs,assignment={},{},{}
        @cache
        def profile(a,x,sa):
            v=[0]*abs(q)
            while a:
                bit=a&-a
                i=bit.bit_length()-1
                v[projection[i]] += sa*(-1 if x&bit else 1)
                a-=bit
            return (plane_canonical if q<0 else canonical)(tuple(v))
        for label,(a,x,b,y) in orientations.items():
            _,sa,sb=label
            va,vb=profile(a,x,sa),profile(b,y,sb)
            pair=tuple(sorted((rows.setdefault(va,len(rows)),rows.setdefault(vb,len(rows)))))
            assignment[label]=pairs.setdefault(pair,len(pairs))
        data=[f"{q} {len(rows)} {len(pairs)}"]
        data.extend(" ".join(map(str,v)) for v in rows)
        data.extend(f"{a} {b}" for a,b in pairs)
        result=subprocess.run([str(binary.resolve())],input="\n".join(data)+"\n",text=True,
                              stdout=subprocess.PIPE,check=True).stdout.split()
        if len(result)!=len(pairs) or any(x not in {"0","1"} for x in result):
            raise ValueError("incorrect signature enumeration")
        passing={label for label,i in assignment.items() if result[i]=="1"}
        accepted &= passing
        print(f"q={name}: {result.count('1')}/{len(pairs)} projected pairs pass; "
              f"{len(passing)}/{len(orientations)} orientations pass, "
              f"{len(accepted)} cumulative in {len({i for i,_,_ in accepted})} templates",flush=True)
    print("Cumulative template sizes",dict(sorted(Counter(lines[i][0] for i in {j for j,_,_ in accepted}).items())))


if __name__=="__main__":
    characterize(Path(sys.argv[1]),Path(sys.argv[2]))
