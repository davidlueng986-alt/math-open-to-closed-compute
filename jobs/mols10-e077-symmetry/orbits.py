#!/usr/bin/env python3
"""Orbit representatives of {L1[1,0], L2[1,0]} under C(p)_0.
No third-square existence assumption. Preserves the original 12 cycle shards.
"""
from itertools import combinations
import json
from pathlib import Path

def partitions(n, lo=2):
    if n == 0:
        yield ()
    for a in range(lo, n+1):
        for tail in partitions(n-a, a):
            yield (a,)+tail

def permutation(parts):
    p=[]; cycles=[]; start=0
    for size in parts:
        cyc=list(range(start,start+size));cycles.append(cyc)
        p.extend(cyc[1:]+cyc[:1]);start+=size
    return p,cycles

def generators(parts):
    p,cycles=permutation(parts);n=len(p);gens=[]
    # Any commuting permutation fixing 0 fixes the cycle containing 0 pointwise.
    # Other cycles of equal length may be permuted, and rotated independently.
    for cyc in cycles[1:]:
        g=list(range(n))
        for x in cyc:g[x]=p[x]
        gens.append(g)
    sizes=sorted({len(c) for c in cycles[1:]})
    for size in sizes:
        same=[c for c in cycles[1:] if len(c)==size]
        for ca,cb in zip(same,same[1:]):
            g=list(range(n))
            for a,b in zip(ca,cb):g[a]=b;g[b]=a
            gens.append(g)
    for g in gens:
        assert sorted(g)==list(range(n)) and g[0]==0
        assert all(g[p[x]]==p[g[x]] for x in range(n))
    return gens

def pair_orbits(parts):
    p,_=permutation(parts);n=len(p);gens=generators(parts)
    remaining=set(combinations(range(2,n),2));orbits=[]
    while remaining:
        rep=min(remaining); orbit={rep};queue=[rep]
        for a,b in queue:
            for g in gens:
                q=tuple(sorted((g[a],g[b])))
                if q not in orbit:orbit.add(q);queue.append(q)
        assert orbit<=remaining
        remaining-=orbit;orbits.append({'representative':list(rep),'members':[list(q) for q in sorted(orbit)]})
    return orbits

def main():
    rows=[]
    for i,parts in enumerate(partitions(10)):
        rows.append({'shard':i,'partition':parts,'representative_count':len(pair_orbits(parts)),
                     'generators':generators(parts),'orbits':pair_orbits(parts)})
    result={'method':'centralizer of canonical row permutation, fixing symbol 0; last two squares interchangeable',
            'unreduced_cubes':28*12,'representatives':sum(r['representative_count'] for r in rows),'shards':rows}
    Path(__file__).with_name('orbits.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='shards'}))
    for r in rows:print(r['shard'],r['partition'],r['representative_count'],[o['representative'] for o in r['orbits']])
if __name__=='__main__':main()
