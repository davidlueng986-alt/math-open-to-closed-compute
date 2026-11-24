"""Restrict the seven-entry templates by the length-19 and small quotient equations."""

import argparse
from collections import Counter
from functools import cache
from itertools import product
from math import isqrt
from pathlib import Path
import subprocess


def projections(support, negative, q):
    return tuple(sum((-1 if negative>>i&1 else 1) for i in range(j,63,q) if support>>i&1)
                 for j in range(q))


@cache
def canonical(row):
    n = len(row)
    return min(tuple(row[(i+step*j)%n] for j in range(n)) for i in range(n) for step in (1,-1))


def orientation_ok(za, zb, weight):
    # The sums of (QR-NQR)/2 are constrained by the parities of the complements.
    required = 126 + 2*(za+zb) - 19*(za*za+zb*zb)
    if required < 0:
        return False
    for d in range((63-weight)%2, isqrt(required)+1, 2):
        e = isqrt(required-d*d)
        if d*d+e*e == required and e%2 == weight%2:
            return True
    return False


def vertical57(orientations, binary):
    rows, pairs, assignment = {}, {}, {}
    for label,(a,x,b,y) in orientations.items():
        _,sa,sb = label
        profile = []
        for support,neg,sign in ((a,x,sa),(b,y,sb)):
            signed = projections(support,neg,3)
            weights = projections(support,0,3)
            # D3 acts as all permutations on three bins. Reversal only changes the
            # sign of the skew component, which can also be reversed by D -> -D.
            bins = sorted(zip((sign*n for n in signed),weights))
            row = tuple(n for n,w in bins) + tuple(w for n,w in bins)
            profile.append(rows.setdefault(row,len(rows)))
        pair = tuple(sorted(profile))
        assignment[label] = pairs.setdefault(pair,len(pairs))
    data = [f"{len(rows)} {len(pairs)}"]
    data += [" ".join(map(str,row)) for row in rows]
    data += [f"{a} {b}" for a,b in pairs]
    got = subprocess.run([str(binary.resolve())],input="\n".join(data)+"\n",text=True,
                         stdout=subprocess.PIPE,check=True).stdout.split()
    if len(got)!=len(pairs) or any(x not in {"0","1"} for x in got):
        raise ValueError("invalid length-57 output")
    return {label for label,k in assignment.items() if got[k]=="1"},got.count("1"),len(pairs)


def main(templates, binary, quotients, vertical, save=None):
    orientations = {}
    lines = templates.read_text().splitlines()
    for i,line in enumerate(lines):
        weight,a,x,b,y,_ = map(int,line.split())
        za,zb = weight-2*x.bit_count(), 7-weight-2*y.bit_count()
        for sa,sb in product((1,-1),repeat=2):
            if orientation_ok(sa*za,sb*zb,weight):
                orientations[i,sa,sb] = (a,x,b,y)
    accepted = set(orientations)
    for q in quotients:
        rows, pairs, assignment = {}, {}, {}
        for label,(a,x,b,y) in orientations.items():
            i,sa,sb = label
            profile = []
            for support,neg,sign in ((a,x,sa),(b,y,sb)):
                v = canonical(tuple(sign*t for t in projections(support,neg,q)))
                profile.append(rows.setdefault(v,len(rows)))
            pair = tuple(sorted(profile))
            assignment[label] = pairs.setdefault(pair,len(pairs))
        data = [f"{q} {len(rows)} {len(pairs)}"]
        data += [" ".join(map(str,row)) for row in rows]
        data += [f"{a} {b}" for a,b in pairs]
        output = subprocess.run([str(binary.resolve())],input="\n".join(data)+"\n",text=True,
                                stdout=subprocess.PIPE,check=True).stdout.split()
        if len(output) != len(pairs) or any(x not in {"0","1"} for x in output):
            raise ValueError("invalid quotient search output")
        surviving = {label for label,k in assignment.items() if output[k]=="1"}
        accepted &= surviving
        print(f"q={q}: {output.count('1')}/{len(pairs)} projected template pairs admit signs; "
              f"{len(surviving)}/{len(orientations)} orientations pass, "
              f"{len(accepted)} cumulative orientations in {len({k[0] for k in accepted})} templates",
              flush=True)
    if vertical:
        surviving,count,total = vertical57(orientations,vertical)
        accepted &= surviving
        print(f"q=57: {count}/{total} projected template pairs admit signs; "
              f"{len(surviving)}/{len(orientations)} orientations pass, "
              f"{len(accepted)} cumulative orientations in {len({k[0] for k in accepted})} templates",flush=True)
    if save:
        signs = list(product((1,-1),repeat=2))
        save.write_text("".join(format(sum(1<<j for j,(a,b) in enumerate(signs) if (i,a,b) in accepted),"x")
                                for i in range(len(lines)))+"\n")
    print("Cumulative template sizes",dict(sorted(Counter(
        int(lines[i].split()[0]) for i in {k[0] for k in accepted}
    ).items())))


if __name__ == "__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("templates",type=Path)
    p.add_argument("binary",type=Path)
    p.add_argument("quotients",type=int,nargs="+",choices=(3,7,9))
    p.add_argument("--vertical",type=Path,help="length-57 Fourier-signature binary")
    p.add_argument("--write-orientations",type=Path,help="one 4-bit orientation mask per template")
    args=p.parse_args()
    main(args.templates,args.binary,args.quotients,args.vertical,args.write_orientations)
