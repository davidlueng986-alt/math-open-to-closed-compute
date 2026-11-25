#!/usr/bin/env python3
"""Proof-producing optimization for D6/D7/D8. All added constraints necessary.
Conditional on the already checked complete D5 exclusion (see README).
"""
import argparse,itertools,json,random,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ramsey-r310-d9-kaggle-v4'))
import d9
sys.path.insert(0,str(HERE.parent/'ramsey-r310-repair-v3'))
import repair
from pysat.solvers import Solver
N=40;e=d9.e;pairs=d9.pairs
E={6:118,7:104,8:95,9:86}
ET={23:35,24:40,25:46,26:52,27:61,28:68}
V=(6,7,8,9)
R={1:1,2:3,3:6,4:9,5:14,6:18,7:23,8:28,9:36}
TRUE=781
def comps(n,k):
    if k==1:yield (n,);return
    for a in range(n+1):
        for b in comps(n-a,k-1):yield (a,)+b
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def profiles():
    for n in comps(40,4):
        D=dot(n,(3,2,1,0))
        if D%2 or D>38:continue
        m=180-D//2;L=[max(0,9*k+E[k]-m) for k in V]
        good=True
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
def support(d,q):
    # Counts for X=N(0)-1 and Y=N(1)-0; these are disjoint since triangle-free.
    xs=[x for x in comps(d-1,4) if all(not t or k>=q for t,k in zip(x,V))]
    ys=list(comps(q-1,4));nt=40-d-q;out=[]
    for n,m in profiles():
        a=list(n);a[d-6]-=1;a[q-6]-=1
        if min(a)<0:continue
        ok=False
        for x in xs:
            if any(i>j for i,j in zip(x,a)):continue
            sx=dot(x,V);h0=m-q-sx
            if not E[d]<=h0<=180-9*d:continue
            av=[i-j for i,j in zip(a,x)]
            for y in ys:
                if any(i>j for i,j in zip(y,av)):continue
                sy=dot(y,V);h1=m-d-sy
                if not E[q]<=h1<=4*(39-q):continue
                # Let t=e(X,Y). Then e(T)=m-1-sx-sy+t.
                # Nonadjacent pair (1,x) has at most deg(x)+q-11 common
                # neighbors, including vertex 0, hence deg_Y(x)<=deg(x)+q-12.
                lo=max(0,ET[nt]-m+1+sx+sy)
                hi=min((d-1)*(q-1),sx+(d-1)*(q-12),sy+(q-1)*(d-12),4*nt-m+1+sx+sy)
                if lo<=hi:ok=True;break
            if ok:break
        if ok:out.append((n,m))
    return out
def plan():
    out=[]
    for d in (6,7,8):
        for q in V:
            s=support(d,q);ms=sorted({m for n,m in s});assert ms
            # Four exhaustive disjoint total-edge bands; split by distinct m.
            for k in range(4):
                sub=ms[k*len(ms)//4:(k+1)*len(ms)//4]
                if sub:out.append(dict(d=d,q=q,band=k,lo=sub[0],hi=sub[-1],m_values=sub,
                    profile_count=sum(m in sub for n,m in s)))
    return out
class Enc(d9.Enc,repair.Encoding):
    def brange(self,xs,lo,hi):
        known=sum(self.val(x) is True for x in xs)
        rem=[x for x in xs if self.val(x) is None]
        repair.Encoding.range(self,rem,lo-known,hi-known)
    def unary(self,xs,lim,exact=True):
        """Balanced totalizer: exact thresholds or sound forward thresholds.
        Forward mode: >=k actual true inputs forces output k; exact outputs
        are a satisfying extension, so upper-bound uses preserve all models.
        """
        if lim<=0:return []
        known=sum(self.val(x) is True for x in xs)
        x=[x for x in xs if self.val(x) is None]
        if known>=lim:return [TRUE]*lim
        cap=lim-known
        def gt(a,k):
            return TRUE if k<=0 else a[k-1] if k<=len(a) else -TRUE
        def build(a):
            if len(a)<=1:return a
            A=build(a[:len(a)//2]);B=build(a[len(a)//2:])
            C=[self.var() for _ in range(min(cap,len(A)+len(B)))]
            for i in range(len(A)+1):
                for j in range(len(B)+1):
                    k=i+j
                    if 0<k<=len(C):self.add([-gt(A,i),-gt(B,j),gt(C,k)])
                    if exact and k+1<=len(C):self.add([gt(A,i+1),gt(B,j+1),-gt(C,k+1)])
            return C
        return [TRUE]*known+build(x)
    def ge(self,a,k):return TRUE if k<=0 else a[k-1] if k<=len(a) else -TRUE
def groups(d,q):
    X=list(range(2,d+1));Y=list(range(d+1,d+q));T=list(range(d+q,40))
    A=[1]+X;B=[0]+Y
    return X,Y,T,A,B
def formula(d,q,band):
    s=support(d,q);s=[(n,m) for n,m in s if band['lo']<=m<=band['hi']]
    assert s
    z=Enc();X,Y,T,A,B=groups(d,q);H0=Y+T;H1=X+T
    for i in range(1,N):z.fix(e(0,i) if i in A else -e(0,i))
    for i in range(2,N):z.fix(e(1,i) if i in B else -e(1,i))
    for C in [A,B]:
        for i,j in itertools.combinations(C,2):z.fix(-e(i,j))
    for i,j,k in itertools.combinations(range(N),3):z.add([-e(i,j),-e(i,k),-e(j,k)])
    deg={}
    for i in range(N):
        ds=[e(i,j) for j in range(N) if j!=i]
        deg[i]=z.unary(ds,10,True)
        low=q if i in X else 6
        if i in (0,1):low=d if i==0 else q
        z.add([z.ge(deg[i],low)]);z.add([-z.ge(deg[i],10)])
    # Exact histogram membership: one listed necessary profile must match.
    count={}
    for k in V:
        exact=[z.AND([z.ge(deg[i],k),-z.ge(deg[i],k+1)]) for i in range(N)]
        count[k]=z.unary(exact,max(n[k-6] for n,m in s)+1,True)
    sels=[]
    for n,m in s:
        h=z.var();sels.append(h)
        for k,num in zip(V,n):
            z.add([-h,z.ge(count[k],num)]);z.add([-h,-z.ge(count[k],num+1)])
    z.add(sels)
    z.brange(list(d9.edge.values()),band['lo'],band['hi'])
    z.brange([e(i,j) for i,j in itertools.combinations(H0,2)],E[d],180-9*d)
    z.brange([e(i,j) for i,j in itertools.combinations(H1,2)],E[q],4*len(H1))
    z.brange([e(i,j) for i,j in itertools.combinations(T,2)],ET[len(T)],4*len(T))
    # Both root antineighborhoods have alpha<=8, hence min internal degree.
    for H,k in [(H0,d),(H1,q)]:
        for i in H:
            z.bounds([e(i,j) for j in H if i!=j],11-k,8)
    # All pairs: saturation, exact degree-aware upper bound on codegrees.
    # If i,j nonadjacent, common antineighborhood has <=27 vertices:
    # deg(i)+deg(j)-codeg(i,j)>=11. Adjacent pairs have codegree zero.
    for i,j in pairs:
        if z.val(e(i,j)) is True:continue
        ws=[z.AND([e(i,k),e(j,k)]) for k in range(N) if k not in (i,j)]
        z.add([e(i,j)]+ws)
        cs=z.unary(ws,8,False)
        for a in V:
            for b in V:
                z.add([z.ge(deg[i],a+1),z.ge(deg[j],b+1),-z.ge(cs,a+b-10)])
    # Deficit-weighted neighbor sums: each v of degree k has
    # e(G_v)=m-9k+eps(v)>=E[k]; use upper endpoint of m-band.
    lim=max(0,max(E[k]+9*k-band['hi'] for k in V))
    if lim:
        for i in range(N):
            ws=[z.AND([e(i,j),-z.ge(deg[j],k+1)]) for j in range(N) if i!=j for k in (6,7,8)]
            eps=z.unary(ws,lim,True)
            for k in V:
                l=E[k]+9*k-band['hi']
                if l>0:z.add([-z.ge(deg[i],k),z.ge(deg[i],k+1),z.ge(eps,l)])
    # Neighborhood-pattern inequalities. A is independent.
    # H_B has no neighbors in A\\B. H_B union B has alpha<=9-|A|+|B|.
    # H_B intersect N(a) is independent, giving much tighter class bounds.
    for nb,H in [(A,H0),(B,H1)]:
        k=len(nb)
        for b in range(1,min(4,k-2)+1):
            for sub in itertools.combinations(nb,b):
                omit=[u for u in nb if u not in sub]
                w=[z.AND([-e(v,u) for u in omit]) for v in H]
                r=10-k+b
                z.am(w,R[r]-1-b)
                for a in sub:
                    z.am([z.AND([t,e(v,a)]) for t,v in zip(w,H)],9-k+b)
    # Lex max adjacency matrix among permutations fixing 0,1 and preserving
    # X,Y,T. Unlike a conflicting independent sorting, all these constraints
    # hold simultaneously in one lex-max representative.
    for C in (X,Y,T):
        for i,j in zip(C,C[1:]):
            ks=[k for k in range(N) if k not in (i,j)]
            z.lex([e(i,k) for k in ks],[e(j,k) for k in ks])
    return z,s
def selftest():
    expected={(6,6):550,(6,7):555,(6,8):248,(6,9):66,(7,6):622,(7,7):702,(7,8):695,(7,9):305,(8,6):672,(8,7):749,(8,8):749,(8,9):335}
    assert len(list(profiles()))==931
    for (d,q),n in expected.items():assert len(support(d,q))==n
    # Independently computed JS profile count and exhaustive truth tables.
    for n in range(1,8):
        for cap in range(1,n+1):
            for exact in (True,False):
                z=Enc();xs=[(-i if i%2 else i) for i in range(1,n+1)];u=z.unary(xs,cap,exact)
                with Solver(name='cadical195',bootstrap_with=z.f.clauses) as s:
                    for b in itertools.product((0,1),repeat=n):
                        ass=[x if v else -x for x,v in zip(xs,b)]
                        want=[l if sum(b)>=k else -l for k,l in enumerate(u,1)]
                        assert s.solve(assumptions=ass+want)
                        for k,l in enumerate(u,1):
                            if sum(b)>=k:assert not s.solve(assumptions=ass+[-l])
                            elif exact:assert not s.solve(assumptions=ass+[l])
    print('PASS: exact/forward totalizer truth tables; 931 profiles; 12 support counts',flush=True)
def verify_graph(g,d,q,b):
    assert len(g)==N and all(6<=x.bit_count()<=9 for x in g)
    assert g[0].bit_count()==d and g[1].bit_count()==q
    assert g[0]>>1&1
    assert all(not(g[i]&g[j]) for i,j in pairs if g[i]>>j&1)
    m=sum(x.bit_count() for x in g)//2
    assert b['lo']<=m<=b['hi']
    for j in d9.bits(g[0]):assert g[j].bit_count()>=q
    H=[i for i in range(1,N) if not(g[0]>>i&1)]
    h=sum((g[i]>>j)&1 for i,j in itertools.combinations(H,2))
    assert E[d]<=h<=180-9*d
def solve(a):
    b=next(x for x in plan() if (x['d'],x['q'],x['band'])==(a.d,a.q,a.band))
    out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
    z,s=formula(a.d,a.q,b);f=z.f;base_n=f.nv;base_c=len(f.clauses)
    X,Y,T,A,B=groups(a.d,a.q);H0=Y+T;H1=X+T
    result=dict(branch=f'D{a.d}-N{a.q}-M{b["lo"]}-{b["hi"]}',status='OPEN',band=b,base_vars=base_n,base_clauses=base_c,models=0,cuts=0)
    d9.save(out/'result.json',result);print(json.dumps(result),flush=True)
    seen=set();rng=random.Random(610000+a.d*1000+a.q*100+a.band)
    start=time.monotonic()
    def projected(ss):
        c=d9.cut(ss)
        if any(z.val(x) is True for x in c):return None
        return tuple(x for x in c if z.val(x) is None)
    with open(out/'cuts.jsonl','w',buffering=1) as fp:
        def seed(ss):
            ss=tuple(sorted(ss));c=projected(ss)
            if c is not None and c not in seen:
                seen.add(c);f.append(list(c));fp.write(json.dumps(ss)+'\n')
        # Complete independent-set constraints within X union Y, and full
        # root neighborhoods with remaining compatible vertices.
        for ss in itertools.combinations(X+Y,10):seed(ss)
        for nb,H in [(A,H0),(B,H1)]:
            k=len(nb)
            for ss in itertools.combinations(H,10-k):seed(tuple(nb)+ss)
            if k>=7:
                for sub in itertools.combinations(nb,k-1):
                    # Avoid prohibitively large static orbit at d=7, cap 60k.
                    if len(seen)>60000:break
                    for ss in itertools.combinations(H,11-k):seed(tuple(sub)+ss)
        for path in a.reuse:
            if Path(path).exists():
                with open(path) as fi:
                    for i,l in enumerate(fi):
                        if i>=a.reuse_limit:break
                        seed(tuple(json.loads(l)))
        result['cuts']=len(seen);result['initial_cuts']=len(seen)
        d9.save(out/'result.json',result);print(json.dumps(result),flush=True)
        with Solver(name='cadical195',bootstrap_with=f.clauses) as sol:
            while time.monotonic()-start<a.seconds and len(seen)<a.cut_cap:
                sol.conf_budget(50000);st=sol.solve_limited()
                if st is None:continue
                if st is False:result['status']='UNSAT_PENDING_REPLAY';break
                g=d9.graph(sol.get_model());verify_graph(g,a.d,a.q,b);result['models']+=1
                bad=set()
                # Target cuts at each known independent root neighborhood,
                # both antineighborhoods, then the unrestricted graph.
                for verts,k,prefix,cap in [(H0,9,(0,),256),(H1,9,(1,),256),(range(N),10,(),512)]:
                    for ss in d9.independent(g,verts,k,cap,rng):bad.add(tuple(sorted(prefix+ss)))
                if not bad:
                    assert not list(d9.independent(g,range(N),10,1))
                    (out/'witness.txt').write_text(''.join(''.join(str(g[i]>>j&1) for j in range(N))+'\n' for i in range(N)))
                    result['status']='WITNESS_PENDING_INDEPENDENT_REPLAY';break
                new=0
                for ss in sorted(bad):
                    assert all(not(g[i]>>j&1) for i,j in itertools.combinations(ss,2))
                    c=projected(ss);assert c is not None
                    if c in seen:continue
                    seen.add(c);sol.add_clause(list(c));f.append(list(c));fp.write(json.dumps(ss)+'\n');new+=1
                assert new
                result['cuts']=len(seen)
                if result['models']%10==0:d9.save(out/'result.json',result);print(json.dumps(result),flush=True)
    if result['status']=='UNSAT_PENDING_REPLAY':
        result.update(repair.proof(f,out,a.proof_seconds))
        result['status']='CERTIFIED_UNSAT' if result['certificate']=='VERIFIED_UNSAT' else 'OPEN_UNCERTIFIED_UNSAT'
    result['seconds']=time.monotonic()-start;d9.save(out/'result.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--plan',action='store_true');p.add_argument('--selftest',action='store_true')
    p.add_argument('--d',type=int);p.add_argument('--q',type=int);p.add_argument('--band',type=int)
    p.add_argument('--out',default='out');p.add_argument('--reuse',action='append',default=[])
    p.add_argument('--reuse-limit',type=int,default=60000);p.add_argument('--seconds',type=int,default=2400)
    p.add_argument('--proof-seconds',type=int,default=480);p.add_argument('--cut-cap',type=int,default=650000)
    a=p.parse_args()
    if a.selftest:selftest()
    elif a.plan:print(json.dumps(plan(),separators=(',',':')))
    else:solve(a)
