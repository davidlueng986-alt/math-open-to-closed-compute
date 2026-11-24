"""Check signed templates by scalar correlations and the support census by Burnside."""

from collections import Counter
from itertools import product
from hashlib import sha256
from math import gcd
from pathlib import Path
import re
import sys


def group(plane):
    if not plane:
        permutations = [[i*u%63 for i in range(63)] for u in range(1,63) if gcd(u,63)==1]
        return permutations, [[(i+t)%63 for i in range(63)] for t in range(63)]
    points = [(i%9//3,i%3,i%7) for i in range(63)]
    index = {v:i for i,v in enumerate(points)}
    translations = [[index[(x+a)%3,(y+b)%3,(c+d)%7] for x,y,c in points] for a,b,d in points]
    permutations = []
    for x,y in product(range(3),repeat=2):
        if (x,y)==(0,0): continue
        line={(k*x%3,k*y%3) for k in range(3)}
        for v,w in product(range(3),repeat=2):
            if (v,w) in line: continue
            for u in range(1,7):
                permutations.append([index[(a*x+b*v)%3,(a*y+b*w)%3,c*u%7] for a,b,c in points])
    return permutations, translations


def orbit_counts(permutations, translations):
    accumulated = [0]*8
    for perm in permutations:
        for tr in translations:
            unseen = set(range(63))
            counts = [1]+[0]*7
            while unseen:
                i = next(iter(unseen))
                length = 0
                while i in unseen:
                    unseen.remove(i)
                    length += 1
                    i = tr[perm[i]]
                for k in range(7,length-1,-1):
                    counts[k] += counts[k-length]
            accumulated = [x+y for x,y in zip(accumulated,counts)]
    size = 63*len(permutations)
    if any(x%size for x in accumulated):
        raise ValueError("nonintegral affine orbit count")
    return [x//size for x in accumulated]


def check(templates, log, plane=False):
    perm,tr = group(plane)
    lags = [s for s in range(1,63) if s<tr[s].index(0)]
    digest = ("e4296827f099f90b6c6449052ca286ba5c13f0ece2e1d94518b458892ab65cd3" if plane else
              "2313b2bcde311bb1aa9502ed027073fd50c73cdfc7110d8270b82fb42d5b301b")
    counts = Counter()
    if sha256(templates.read_bytes()).hexdigest() != digest:
        raise ValueError("template list differs from the archived census")
    for line in templates.read_text().splitlines():
        k,a,x,b,y,h = map(int,line.split())
        if (a.bit_count(), b.bit_count())!=(k,7-k) or x&~a or y&~b:
            raise ValueError("invalid signs or support")
        rows = [[(s>>i&1)*(1-2*(n>>i&1)) for i in range(63)] for s,n in ((a,x),(b,y))]
        corr = [sum(row[i]*row[tr[t][i]] for row in rows for i in range(63)) for t in lags]
        if set(corr)-{0,-1} or corr.count(-1)!=h or h not in (1,3):
            raise ValueError("sparse signed autocorrelation mismatch")
        counts[k] += 1
    orbit = orbit_counts(perm,tr)
    reported = {int(k):(int(r),int(s)) for k,r,s in
                re.findall(r"(\d+) reps=(\d+) paired=\d+ signed=(\d+)",log.read_text())}
    expected = {4:1095,5:677,6:12,7:30} if plane else {4:2804,5:977,6:15,7:46}
    if counts!=expected or reported!={k:(orbit[k],counts[k]) for k in range(4,8)}:
        raise ValueError("Burnside count or signed template count disagrees")
    print("Affine support orbit counts and direct signed correlations agree:",reported)


if __name__ == "__main__":
    check(Path(sys.argv[1]),Path(sys.argv[2]), "--plane" in sys.argv[3:])
