#!/usr/bin/env python3
"""Exact bounded theorem: no W can be obtained from seed31002 by <=4
added edges, even with unlimited deletions. All 10 independent sets
must be hit. The 1-old-edge 10-sets then force a triangle in all cases."""
from pathlib import Path
from itertools import combinations,product
from collections import defaultdict,Counter
import argparse,json
p=argparse.ArgumentParser();p.add_argument('near');a=p.parse_args()
rows=(Path(__file__).resolve().parent/'seed31002.txt').read_text().splitlines();N=40
assert len(rows)==N and all(len(s)==N and set(s)<=set('01') for s in rows)
A=[sum(1<<j for j,c in enumerate(row) if c=='1') for row in rows]
assert all(not(A[i]>>i&1) for i in range(N)) and all((A[i]>>j&1)==(A[j]>>i&1) for i,j in combinations(range(N),2))
E=[(i,j) for i,j in combinations(range(N),2) if A[i]>>j&1];ES=set(E)
NE=[(i,j) for i,j in combinations(range(N),2) if not A[i]>>j&1]
assert len(E)==180 and len(NE)==600 and all(a.bit_count()==9 for a in A)
assert all(not(A[i]&A[j]) for i,j in E)
old=defaultdict(int);added=defaultdict(int);bad=[];idx=0;seen=set()
for l in Path(a.near).read_text().splitlines():
    cost,*s=map(int,l.split());assert len(s)==10 and s==sorted(set(s)) and min(s)>=0 and max(s)<40
    assert tuple(s) not in seen;seen.add(tuple(s))
    ps=list(combinations(s,2));es=[p for p in ps if p in ES]
    assert len(es)==cost
    if cost==0:bad.append(set(s))
    else:
        assert cost==1;old[es[0]]|=1<<idx
        for p in ps:
            if p!=es[0]:added[p]|=1<<idx
        idx+=1
assert len(bad)==10 and idx==18015
classes=defaultdict(list)
for u,v in NE:
    m=sum(1<<i for i,s in enumerate(bad) if u in s and v in s)
    if m:classes[m].append((u,v))
full=(1<<len(bad))-1
counts={};reject=Counter();survivors=[]
# If <=4 additions cover all 10 original I10s, all four masks are nonzero
# and distinct: otherwise at most three distinct nonzero masks would cover.
for k in range(1,5):
    n=0
    for masks in combinations(classes,k):
        union=0
        for m in masks:union|=m
        if union!=full:continue
        for es in product(*(classes[m] for m in masks)):
            n+=1;hit=0
            for p in es:hit|=added[p]
            # Every unhit 10-set having exactly one old edge forces it to remain.
            mandatory=[p for p in E if old[p]&~hit]
            g=[0]*N
            for i,j in mandatory+list(es):g[i]|=1<<j;g[j]|=1<<i
            if any(g[i]&g[j] for i,j in mandatory+list(es)):reject['mandatory_triangle']+=1
            elif any(x.bit_count()>9 for x in g):reject['mandatory_degree']+=1
            else:survivors.append(es)
    counts[k]=n
assert counts=={1:0,2:0,3:0,4:2475}
assert reject['mandatory_triangle']==2475 and not survivors
print(json.dumps(dict(status='EXACT_UNSAT_LOCAL_ADDITIONS_LE_4',cover_counts=counts,rejection_counts=reject,survivors=survivors),indent=2))
