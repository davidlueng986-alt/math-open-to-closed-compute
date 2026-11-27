#!/usr/bin/env python3
"""Exact necessary root-group filter; not a solver or a closure certificate."""
import argparse, hashlib, itertools, json, zipfile
from functools import lru_cache
from pathlib import Path
V=(6,7,8,9); E={6:118,7:104,8:95,9:86}; ET={23:35,24:40,25:46,26:52,27:61,28:68}
@lru_cache(None)
def comps(n,k=4):
    if k==1:return ((n,),)
    return tuple((i,)+s for i in range(n+1) for s in comps(n-i,k-1))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def c2(n):return n*(n-1)//2
def min_pairs(total,n):
    q,r=divmod(total,n);return (n-r)*c2(q)+r*c2(q+1)
@lru_cache(None)
def types(n,m,k):
    h=39-k;out=[]
    for a in comps(k):
        if any(a[j]>n[j]-(V[j]==k) for j in range(4)):continue
        sx=dot(a,V);cross=sx-k
        if not E[k]<=m-sx<=4*h or cross<2*h-k*(10-k):continue
        hn=[n[j]-a[j]-(V[j]==k) for j in range(4)]
        caps=[min(k,l,k+l-11) for l in V]
        if not h<=cross<=dot(hn,caps):continue
        if sum(hn[j] for j in range(4) if caps[j]==1)>k*(10-k):continue
        out.append(a)
    return tuple(out)
@lru_cache(None)
def feasible(n,m,d,q):
    nx,ny,nt=d-1,q-1,40-d-q
    avail=tuple(n[i]-(V[i]==d)-(V[i]==q) for i in range(4))
    if min(avail)<0:return (),()
    xx=[];yy=[]
    for a in types(n,m,d):
        x=tuple(a[i]-(V[i]==q) for i in range(4))
        if min(x)<0 or any(x[i]>avail[i] or x[i] and V[i]<q for i in range(4)):continue
        sx=dot(x,V);h=m-q-sx
        if E[d]<=h<=min(180-9*d,(7*(39-d)+d*(10-d))//2):xx.append((x,sx))
    for a in types(n,m,q):
        y=tuple(a[i]-(V[i]==d) for i in range(4))
        if min(y)<0 or any(y[i]>avail[i] for i in range(4)):continue
        sy=dot(y,V);h=m-d-sy
        if E[q]<=h<=min(4*(39-q),(7*(39-q)+q*(10-q))//2):yy.append((y,sy))
    old=set();new=set()
    for x,sx in xx:
        ax=tuple(avail[i]-x[i] for i in range(4))
        for y,sy in yy:
            if any(y[i]>ax[i] for i in range(4)):continue
            z=tuple(ax[i]-y[i] for i in range(4))
            lo=max(0,ET[nt]-m+1+sx+sy)
            hi=min(nx*ny,sx+nx*(q-12),sy+ny*(d-12),4*nt-m+1+sx+sy)
            if lo>hi:continue
            old.update(range(lo,hi+1))
            capx=sum(z[i]*min(nx,V[i]+d-11) for i in range(4))
            capy=sum(z[i]*min(ny,V[i]+q-11) for i in range(4))
            lo2=max(lo,sx-nx-capx,sy-ny-capy);hi2=min(hi,sx-nx-nt,sy-ny-nt)
            bx=(nx-1)*sx-12*c2(nx);by=(ny-1)*sy-12*c2(ny)
            for t in range(lo2,hi2+1):
                xt=sx-nx-t;yt=sy-ny-t
                if min_pairs(xt,nt)+min_pairs(t,ny)>bx:continue
                if min_pairs(yt,nt)+min_pairs(t,nx)>by:continue
                new.add(t)
    return tuple(sorted(old)),tuple(sorted(new))
def key(t):return hashlib.sha256(json.dumps({k:v for k,v in t.items() if k!='key'},sort_keys=True,separators=(',',':')).encode()).hexdigest()
def screen(plan):
    results=[]
    for t in plan['tasks']:
        assert key(t)==t['key'];old=new=0;surv=[]
        for n in t['profiles']:
            assert sum(n)==40 and dot(n,V)==2*t['m']
            aa,bb=feasible(tuple(n),t['m'],t['d'],t['q'])
            a=[v for v in aa if t['tlo']<=v<=t['thi']];b=[v for v in bb if t['tlo']<=v<=t['thi']]
            assert set(b)<=set(a);old+=len(a);new+=len(b)
            if b:surv.append([n,b])
        results.append(dict(task=t['id'],key=t['key'],prior_pairs=old,new_pairs=new,profiles=len(surv),allowed=surv))
    assert len({r['task'] for r in results})==len(results)
    return dict(task_count=len(results),empty_prior=sum(r['prior_pairs']==0 for r in results),empty_new=sum(r['new_pairs']==0 for r in results),prior_pairs=sum(r['prior_pairs'] for r in results),new_pairs=sum(r['new_pairs'] for r in results),tasks=results)
def selftest():
    for total in range(14):
        for k in range(1,6):assert min_pairs(total,k)==min(sum(c2(i) for i in a) for a in comps(total,k))
    for mask in range(1<<9):
        rows=[(mask>>(3*i))&7 for i in range(3)]
        assert sum((rows[i]&rows[j]).bit_count() for i,j in itertools.combinations(range(3),2))==sum(c2(sum((r>>k)&1 for r in rows)) for k in range(3))
    print('PASS: integer convexity and summed codegree identity',flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--plan',required=True);p.add_argument('--out',required=True);a=p.parse_args();selftest()
    if a.plan.endswith('.zip'):
        with zipfile.ZipFile(a.plan) as z:plan=json.loads(z.read('plan.json'))
    else:plan=json.loads(Path(a.plan).read_text())
    r=screen(plan);Path(a.out).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='tasks'}),flush=True)
