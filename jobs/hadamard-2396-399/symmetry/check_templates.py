"""Check signed templates by scalar correlations and the support census by Burnside."""

from collections import Counter
from hashlib import sha256
from math import gcd
from pathlib import Path
import re
import sys


def orbit_counts():
    accumulated = [0]*8
    for unit in range(1,63):
        if gcd(unit,63) != 1:
            continue
        for b in range(63):
            unseen = set(range(63))
            counts = [1]+[0]*7
            while unseen:
                i = next(iter(unseen))
                length = 0
                while i in unseen:
                    unseen.remove(i)
                    length += 1
                    i = (unit*i+b)%63
                for k in range(7,length-1,-1):
                    counts[k] += counts[k-length]
            accumulated = [x+y for x,y in zip(accumulated,counts)]
    if any(x%2268 for x in accumulated):
        raise ValueError("nonintegral affine orbit count")
    return [x//2268 for x in accumulated]


def check(templates, log):
    counts = Counter()
    if sha256(templates.read_bytes()).hexdigest() != "2313b2bcde311bb1aa9502ed027073fd50c73cdfc7110d8270b82fb42d5b301b":
        raise ValueError("template list differs from the archived census")
    for line in templates.read_text().splitlines():
        k,a,x,b,y,h = map(int,line.split())
        if (a.bit_count(), b.bit_count())!=(k,7-k) or x&~a or y&~b:
            raise ValueError("invalid signs or support")
        rows = [[(s>>i&1)*(1-2*(n>>i&1)) for i in range(63)] for s,n in ((a,x),(b,y))]
        corr = [sum(row[i]*row[(i+t)%63] for row in rows for i in range(63)) for t in range(1,32)]
        if set(corr)-{0,-1} or corr.count(-1)!=h or h not in (1,3):
            raise ValueError("sparse signed autocorrelation mismatch")
        counts[k] += 1
    orbit = orbit_counts()
    reported = {int(k):(int(r),int(s)) for k,r,s in
                re.findall(r"(\d+) reps=(\d+) paired=\d+ signed=(\d+)",log.read_text())}
    if counts!={4:2804,5:977,6:15,7:46} or reported!={k:(orbit[k],counts[k]) for k in range(4,8)}:
        raise ValueError("Burnside count or signed template count disagrees")
    print("Affine support orbit counts and direct signed correlations agree:",reported)


if __name__ == "__main__":
    check(Path(sys.argv[1]),Path(sys.argv[2]))
