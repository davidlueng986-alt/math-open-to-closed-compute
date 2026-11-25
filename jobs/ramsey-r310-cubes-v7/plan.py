#!/usr/bin/env python3
"""Exhaustive profile / cross-edge partition. No solver heuristic can drop a task."""
import argparse,json,sys,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ramsey-r310-d678-v6'))
from profile import verified_partition,types,comps,dot,V,E
from branch import supports
def canon(x):return json.dumps(x,sort_keys=True,separators=(',',':'))
def sha(x):return hashlib.sha256(canon(x).encode()).hexdigest()
def save(path,x):
 p=Path(path);tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(x,indent=2)+'\n');tmp.replace(p)
def make(cert,prior,d,q,b,group_size,parts):
 kept=verified_partition(cert)
 prior=json.loads(Path(prior).read_text())
 band=next(x for x in prior if (x['d'],x['q'],x['band'])==(d,q,b))
 prof=sorted((m,list(n)) for n,m in kept if band['lo']<=m<=band['hi'] and supports(n,m,d,q,True))
 assert len(prof)==band['new_count']
 # For every x in X, common neighbors of x and root 1 include root 0.
 # codeg <= deg(x)+q-11, so deg_Y(x)<=q-3; similarly deg_X(y)<=d-3.
 # This is valid for all degrees <=9. No assumptions on actual cross count.
 hi=min((d-1)*(q-1),(d-1)*(q-3),(q-1)*(d-3))
 assert hi>=0
 intervals=[]
 for i in range(parts):
  lo=i*(hi+1)//parts;up=(i+1)*(hi+1)//parts-1
  if lo<=up:intervals.append([lo,up])
 assert [t for lo,up in intervals for t in range(lo,up+1)]==list(range(hi+1))
 groups=[]
 for m in sorted(set(m for m,n in prof)):
  ns=[n for mm,n in prof if mm==m]
  for j in range(0,len(ns),group_size):groups.append((m,ns[j:j+group_size]))
 tasks=[]
 for g,(m,ns) in enumerate(groups):
  for i,(lo,up) in enumerate(intervals):
   task=dict(id=f'D{d}-N{q}-B{b}-P{g:03d}-T{i:02d}',d=d,q=q,band=b,m=m,profiles=ns,tlo=lo,thi=up)
   task['key']=sha(task);tasks.append(task)
 # Independent explicit product check; even infeasible t values are covered.
 expected={(m,tuple(n),t) for m,n in prof for t in range(hi+1)}
 seen=set()
 for x in tasks:
  assert x['key']==sha({k:v for k,v in x.items() if k!='key'})
  for n in x['profiles']:
   for t in range(x['tlo'],x['thi']+1):
    key=(x['m'],tuple(n),t);assert key not in seen;seen.add(key)
 assert seen==expected
 assert len(tasks)<=256, 'Group profiles more coarsely to fit matrix limit'
 return dict(parent=band,profiles=len(prof),cross_max=hi,coverage_pairs=len(expected),tasks=tasks)
if __name__=='__main__':
 a=argparse.ArgumentParser()
 a.add_argument('--cert',required=True);a.add_argument('--prior',required=True);a.add_argument('--out',required=True)
 a.add_argument('--d',type=int,default=6);a.add_argument('--q',type=int,default=9);a.add_argument('--band',type=int,default=3)
 a.add_argument('--group-size',type=int,default=1);a.add_argument('--parts',type=int,default=8)
 p=a.parse_args();assert p.group_size>0 and p.parts>0
 x=make(p.cert,p.prior,p.d,p.q,p.band,p.group_size,p.parts);save(p.out,x)
 print(json.dumps({k:v for k,v in x.items() if k!='tasks'}),flush=True)
