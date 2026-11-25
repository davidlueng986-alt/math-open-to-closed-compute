"""Exact branch support filter; retains v5 band IDs and original boundaries."""
import json, argparse
from pathlib import Path
from profile import *
ET={23:35,24:40,25:46,26:52,27:61,28:68}
def supports(n,m,d,q,strict=True):
 a=list(n);a[d-6]-=1;a[q-6]-=1
 if min(a)<0:return False
 ts=set(types(n,m)) if strict else None
 nt=40-d-q
 for x in comps(d-1,4):
  if any(x[i]>a[i] or x[i] and V[i]<q for i in range(4)):continue
  sx=dot(x,V);h0=m-q-sx
  if not E[d]<=h0<=180-9*d:continue
  ax=tuple(x[i]+(V[i]==q) for i in range(4))
  if strict and (d-6,ax) not in ts:continue
  av=[a[i]-x[i] for i in range(4)]
  for y in comps(q-1,4):
   if any(y[i]>av[i] for i in range(4)):continue
   sy=dot(y,V);h1=m-d-sy
   if not E[q]<=h1<=4*(39-q):continue
   ay=tuple(y[i]+(V[i]==d) for i in range(4))
   if strict and (q-6,ay) not in ts:continue
   lo=max(0,ET[nt]-m+1+sx+sy)
   hi=min((d-1)*(q-1),sx+(d-1)*(q-12),sy+(q-1)*(d-12),4*nt-m+1+sx+sy)
   if strict:
    h0max=(7*(39-d)+d*(10-d))//2;h1max=(7*(39-q)+q*(10-q))//2
    if h0>h0max or h1>h1max:continue
   if lo<=hi:return True
 return False
def build(path):
 kept=verified_partition(path);p=list(profiles());out=[]
 for d in (6,7,8):
  for q in V:
   old=[(n,m) for n,m in p if supports(n,m,d,q,False)]
   new=[(n,m) for n,m in kept if supports(n,m,d,q,True)]
   assert set(new)<=set(old)
   ms=sorted(set(m for n,m in old))
   for k in range(4):
    b=ms[k*len(ms)//4:(k+1)*len(ms)//4];ss=[(n,m) for n,m in new if m in b]
    out.append(dict(d=d,q=q,band=k,lo=b[0],hi=b[-1],old_count=sum(m in b for n,m in old),new_count=len(ss),m_values=sorted({m for n,m in ss})))
 return out
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--cert',required=True);p.add_argument('--out',required=True);a=p.parse_args()
 b=build(a.cert);assert len(b)==48
 Path(a.out).write_text(json.dumps(b,indent=2)+'\n');print(json.dumps(b),flush=True)
