#!/usr/bin/env python3
"""Reuse v5 with exactly checked profile filtering and nested Ramsey dual bounds."""
import argparse,importlib.util,itertools,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
from profile import verified_partition
from branch import supports
s=importlib.util.spec_from_file_location('ramsey_v5',HERE.parent/'ramsey-r310-d678-v5'/'solve.py')
v5=importlib.util.module_from_spec(s);s.loader.exec_module(v5)
E8={21:35,22:42,23:49,24:56,25:65,26:73,27:85}
E9={6:118,7:104,8:95,9:86}
e=v5.e
def strengthen(z,H,k,lo,hi):
 # e(H) exact selector, fixed root structure and singleton upper bound.
 hi=min(hi,(7*len(H)+k*(10-k))//2)
 es=[e(i,j) for i,j in itertools.combinations(H,2)]
 fixed=sum(z.val(x) is True for x in es);free=[x for x in es if z.val(x) is None]
 hb=z.sum_bits(free)
 flags={m:z.AND([x if ((m-fixed)>>i)&1 else -x for i,x in enumerate(hb)])
        for m in range(lo,hi+1) if 0<=m-fixed<2**len(hb)}
 z.add(list(flags.values()))
 mind=len(H)-28
 dh={i:z.unary([e(i,j) for j in H if j!=i],9,True) for i in H}
 lim=max(0,max(E8[len(H)-1-r]+8*r-lo for r in range(mind,9)))
 if lim:
  for i in H:
   # sum over each H-neighbor of (8 - its internal degree in H)
   ws=[z.AND([e(i,j),-z.ge(dh[j],t+1)]) for j in H if j!=i for t in range(mind,8)]
   eps=z.unary(ws,lim,True)
   for r in range(mind,9):
    for m,flag in flags.items():
     need=E8[len(H)-1-r]+8*r-m
     if need>0:z.add([-flag,-z.ge(dh[i],r),z.ge(dh[i],r+1),z.ge(eps,need)])
 # Strong pair codegree cap in dual H, especially near minimum degrees.
 # Apply only for H>=32 and internal degrees at most mind+1.
 if len(H)>=32:
  for i,j in itertools.combinations(H,2):
   if z.val(e(i,j)) is True:continue
   ws=[z.AND([e(i,u),e(j,u)]) for u in H if u not in (i,j)]
   lim2=2*(mind+1)-(len(H)-24)+1
   cs=z.unary(ws,max(0,lim2),False)
   for a in range(mind,mind+2):
    for b in range(mind,mind+2):
     z.add([e(i,j),z.ge(dh[i],a+1),z.ge(dh[j],b+1),-z.ge(cs,a+b-(len(H)-24)+1)])
def main():
 p=argparse.ArgumentParser();p.add_argument('--d',type=int,required=True);p.add_argument('--q',type=int,required=True);p.add_argument('--band',type=int,required=True)
 p.add_argument('--cert',required=True);p.add_argument('--plan',required=True);p.add_argument('--out',required=True)
 p.add_argument('--reuse',action='append',default=[]);p.add_argument('--reuse-limit',type=int,default=60000)
 p.add_argument('--seconds',type=int,default=2400);p.add_argument('--proof-seconds',type=int,default=480);p.add_argument('--cut-cap',type=int,default=650000);a=p.parse_args()
 kept=verified_partition(a.cert);b=json.loads(Path(a.plan).read_text())
 # Independently regenerate this exact band's necessary support, not just trust plan.
 old_plan=v5.plan();bp=next(t for t in old_plan if (t['d'],t['q'],t['band'])==(a.d,a.q,a.band))
 new=[(n,m) for n,m in kept if supports(n,m,a.d,a.q,True)]
 actual=[(n,m) for n,m in new if bp['lo']<=m<=bp['hi']]
 record=next(t for t in b if (t['d'],t['q'],t['band'])==(a.d,a.q,a.band))
 assert len(actual)==record['new_count'] and (bp['lo'],bp['hi'])==(record['lo'],record['hi'])
 out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
 if not actual:
  (out/'result.json').write_text(json.dumps(dict(status='PROVED_NO_NECESSARY_PROFILE',band=record),indent=2)+'\n')
  print((out/'result.json').read_text(),flush=True);return
 orig=v5.formula
 # Original bands unchanged; only remove impossible profiles.
 v5.support=lambda d,q:new if (d,q)==(a.d,a.q) else []
 v5.plan=lambda:old_plan
 def improved(d,q,b):
  z,ss=orig(d,q,b);assert len(ss)==len(actual)
  X,Y,T,A,B=v5.groups(d,q)
  # First dual carries the weighted-Mantel root upper bound; second uses
  # singleton capacity and the total edge band's upper bound.
  strengthen(z,Y+T,d,E9[d],180-9*d)
  minsum=max(6*q,q+2*(39-q)-q*(10-q))
  strengthen(z,X+T,q,E9[q],min(4*(39-q),b['hi']-minsum))
  print(json.dumps(dict(status='NESTED_DUALS_ENCODED',profiles=len(ss),variables=z.f.nv,clauses=len(z.f.clauses))),flush=True)
  return z,ss
 v5.formula=improved
 v5.solve(a)
if __name__=='__main__':main()
