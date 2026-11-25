"""Necessary profile exclusion by local type counts and exact Farkas certificates."""
import itertools,json,time,argparse
from pathlib import Path
from functools import lru_cache
V=(6,7,8,9); E={6:118,7:104,8:95,9:86}
def comps(n,k):
 if k==1:yield (n,);return
 for a in range(n+1):
  for b in comps(n-a,k-1):yield (a,)+b
def dot(a,b):return sum(i*j for i,j in zip(a,b))
def profiles():
 for n in comps(40,4):
  D=dot(n,(3,2,1,0))
  if D%2 or D>38:continue
  m=180-D//2; L=[max(0,9*k+E[k]-m) for k in V];good=True
  for i,k in enumerate(V):
   if not n[i]:continue
   rem=k;u=0
   for j in range(4):
    z=min(rem,n[j]-(i==j));rem-=z;u+=z*(3-j)
   if u<L[i]:good=False;break
  if not good:continue
  if dot(n,L)>sum(n[i]*V[i]*(3-i) for i in range(4)):continue
  if 2*sum(n[i]*(3-i)*L[i] for i in range(4))>D*D:continue
  yield n,m
@lru_cache(None)
def types(n,m):
 out=[]
 for i,k in enumerate(V):
  if not n[i]:continue
  h=39-k
  for a in comps(k,4):
   if any(a[j]>n[j]-(j==i) for j in range(4)):continue
   sx=dot(a,V);cross=sx-k
   if not E[k]<=m-sx<=4*h:continue
   if cross<2*h-k*(10-k):continue
   hn=[n[j]-a[j]-(i==j) for j in range(4)]
   caps=[min(k,l,k+l-11) for l in V]
   if not h<=cross<=dot(hn,caps):continue
   if sum(hn[j] for j in range(4) if caps[j]==1)>k*(10-k):continue
   out.append((i,a))
 return out
P=list(itertools.combinations_with_replacement(range(4),2));D=list(itertools.combinations(range(4),2))
def col(i,a):
 eq=[int(i==j) for j in range(4)]+[(a[j] if i==k else 0)-(a[k] if i==j else 0) for k,j in D]
 ub=[]
 for k,j in P:
  cap=V[k]+V[j]-11
  if k==j:c=a[k]*(a[k]-1);ed=a[k] if i==k else 0
  else:c=a[k]*a[j];ed=a[j] if i==k else 0
  ub.extend([-c-ed,c+cap*ed])
 return eq+ub
def rhs(n):
 b=list(n)+[0]*len(D)
 for k,j in P:
  v=n[k]*(n[k]-1) if k==j else n[k]*n[j]
  b.extend([-v,(V[k]+V[j]-11)*v])
 return b
NE=4+len(D)
def verify(n,m,y):
 ts=types(tuple(n),m);b=rhs(n)
 assert len(y)==len(b) and all(isinstance(v,int) for v in y) and min(y[NE:])>=0
 assert all(dot(col(i,a),y)>=0 for i,a in ts)
 assert dot(y,b)<0
 return True
def check(n,m):
 import numpy as np
 from scipy.optimize import linprog
 ts=types(n,m);b=np.asarray(rhs(n),dtype=float)
 if not ts or any(n[i] and not any(j==i for j,a in ts) for i in range(4)):
  i=next(i for i in range(4) if n[i] and not any(j==i for j,a in ts))
  y=[0]*len(b);y[i]=-1;verify(n,m,y);return y
 A=np.asarray([col(i,a) for i,a in ts],dtype=float).T
 res=linprog(np.zeros(len(ts)),A_eq=A[:NE],b_eq=b[:NE],A_ub=A[NE:],b_ub=b[NE:],bounds=(0,None),method='highs')
 if res.status==0:return None
 if res.status!=2:raise RuntimeError(res.message)
 r=linprog(np.zeros(len(b)),A_ub=np.vstack([-A.T,b]),b_ub=np.r_[np.zeros(len(ts)),-1],bounds=[(None,None)]*NE+[(0,None)]*(len(b)-NE),method='highs')
 if not r.success:raise RuntimeError('dual fail '+r.message)
 for scale in [1000,1000000,1000000000]:
  y=[round(scale*v) for v in r.x]
  for i in range(4):
   mn=min((dot(col(j,a),y) for j,a in ts if j==i),default=0)
   y[i]+=max(0,-mn)
  if dot(y,b)<0:
   verify(n,m,y);return y
 # No floating-point result by itself is allowed to eliminate a profile.
 return None
def verified_partition(path):
 obj=json.loads(Path(path).read_text());p=set(profiles())
 keep={(tuple(n),m) for n,m in obj['surviving']}
 ex={(tuple(c['n']),c['m']) for c in obj['excluded']}
 assert len(ex)==len(obj['excluded']) and len(keep)==len(obj['surviving'])
 assert not ex&keep and ex|keep==p
 for c in obj['excluded']:verify(c['n'],c['m'],c['y'])
 return sorted(keep)
def main():
 p=argparse.ArgumentParser();p.add_argument('--out',required=True);p.add_argument('--verify',action='store_true');a=p.parse_args()
 if not a.verify:
  cert=[];keep=[];ps=list(profiles())
  for n,m in ps:
   y=check(n,m)
   if y is None:keep.append((n,m))
   else:cert.append(dict(n=n,m=m,y=y))
  Path(a.out).write_text(json.dumps(dict(profiles=len(ps),excluded=cert,surviving=keep),separators=(',',':')))
 keep=verified_partition(a.out)
 print(json.dumps(dict(status='EXACT_CERTIFICATES_VERIFIED',profiles=931,excluded=931-len(keep),surviving=len(keep),min_m_with_n6=min(m for n,m in keep if n[0]))),flush=True)
if __name__=='__main__':main()
