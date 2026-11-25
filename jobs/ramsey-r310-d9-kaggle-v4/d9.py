#!/usr/bin/env python3
"""D9 exact case proof search. No timeout or unverified UNSAT counts as closure."""
import argparse,itertools,json,time,random,subprocess,resource,gzip,shutil,hashlib,os
from pathlib import Path
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
N=40
pairs=list(itertools.combinations(range(N),2))
edge={p:i+1 for i,p in enumerate(pairs)}
def e(i,j):return edge[tuple(sorted((i,j)))]
def bits(x):
    while x:
        b=x&-x;yield b.bit_length()-1;x^=b
def groups(c):
    S=list(range(2,2+c));X=list(range(2+c,11));Y=list(range(11,20-c));T=list(range(20-c,40))
    assert len(S)==c and len(X)==len(Y)==9-c and len(T)==20+c
    return S,X,Y,T
EMIN={3:49,4:56,5:65,6:73,7:85}
def mx_bounds(c):
    return EMIN[c]-18-9*c,(9-c)**2
def shards(c,cores=None):
    lo,hi=mx_bounds(c)
    if c==7:
        if cores is not None:
            assert len(cores)==4
            return [dict(kind='core',idx=i,core=s) for i,s in enumerate(cores)]
        return [dict(kind='tdeg',lo=i,hi=i) for i in range(4,8)]
    n=hi-lo+1
    return [dict(kind='xy',lo=lo+i*n//4,hi=lo+(i+1)*n//4-1) for i in range(4) if lo+i*n//4<=lo+(i+1)*n//4-1]
def decode(s):
    s=s.strip().removeprefix('>>graph6<<')
    n=ord(s[0])-63;assert n==27 and len(s)==1+(n*(n-1)//2+5)//6
    a=[0]*n;k=0
    for j in range(n):
        for i in range(j):
            if ((ord(s[1+k//6])-63)>>(5-k%6))&1:a[i]|=1<<j;a[j]|=1<<i
            k+=1
    return a
def independent(a,verts,k,limit=None,rng=None):
    order=list(verts)
    if rng:rng.shuffle(order)
    inv={v:i for i,v in enumerate(order)}
    b=[sum(1<<inv[j] for j in bits(a[v]) if j in inv) for v in order]
    count=0
    def go(p,k,s):
        nonlocal count
        if limit is not None and count>=limit:return
        if k==0:
            count+=1;yield tuple(sorted(s));return
        while p.bit_count()>=k and (limit is None or count<limit):
            x=p&-p;p^=x;i=x.bit_length()-1
            yield from go(p&~b[i],k-1,s+[order[i]])
    yield from go((1<<len(order))-1,k,[])
class Enc:
    def __init__(self):
        self.f=CNF();self.pool=IDPool(start_from=782);self.fixed={781:True}
        self.f.append([781])
    def val(self,l):
        v=self.fixed.get(abs(l));return None if v is None else v==(l>0)
    def fix(self,l):
        v=self.val(l)
        if v is False:raise ValueError('contradictory fixed graph')
        if v is None:self.fixed[abs(l)]=l>0;self.f.append([l])
    def var(self):return self.pool.id()
    def add(self,ls):
        c=set()
        for l in ls:
            v=self.val(l)
            if v is True or -l in c:return
            if v is None:c.add(l)
        self.f.append(sorted(c,key=lambda x:(abs(x),x)))
    def AND(self,ls):
        xs=[]
        for l in ls:
            v=self.val(l)
            if v is False:return -781
            if v is None:xs.append(l)
        if not xs:return 781
        if len(xs)==1:return xs[0]
        z=self.var()
        for l in xs:self.add([-z,l])
        self.add([z]+[-l for l in xs])
        return z
    def am(self,ls,k):
        xs=[]
        for l in ls:
            v=self.val(l)
            if v is True:k-=1
            elif v is None:xs.append(l)
        if k<0:self.add([])
        elif k<len(xs):self.f.extend(CardEnc.atmost(lits=xs,bound=k,vpool=self.pool,encoding=EncType.seqcounter).clauses)
    def al(self,ls,k):self.am([-l for l in ls],len(ls)-k)
    def bounds(self,ls,lo,hi):
        self.am(ls,hi);self.al(ls,lo)
    def lex(self,a,b):
        # Each prefix-equality auxiliary iff the prefix is equal.
        p=781
        for x,y in zip(a,b):
            self.add([-p,x,-y])
            z=self.var()
            self.add([-z,p]);self.add([-z,-x,y]);self.add([-z,x,-y])
            self.add([-p,-x,-y,z]);self.add([-p,x,y,z]);p=z
def formula(c,spec,hall=True):
    S,X,Y,T=groups(c);A=S+X;B=S+Y
    z=Enc()
    for v in range(1,N):z.fix(e(0,v) if v in A else -e(0,v))
    for v in range(2,N):z.fix(e(1,v) if v in B else -e(1,v))
    for u,v in itertools.combinations(A,2):z.fix(-e(u,v))
    for u,v in itertools.combinations(B,2):z.fix(-e(u,v))
    if c==7:
        for u in X:
            for v in Y:z.fix(e(u,v))
    if spec['kind']=='core':
        g=decode(spec['core'])
        assert sum(x.bit_count() for x in g)==170
        assert all(not(g[i]&g[j]) for i in range(27) for j in bits(g[i]))
        assert not list(independent(g,range(27),8,1))
        for i,j in itertools.combinations(range(27),2):z.fix(e(T[i],T[j]) if g[i]>>j&1 else -e(T[i],T[j]))
    # Triangles and degree=9. Internal degree in common antineighborhood <=7
    # and >=c-3 by R(3,7)=23.
    for i,j,k in itertools.combinations(range(N),3):z.add([-e(i,j),-e(i,k),-e(j,k)])
    for v in range(N):z.bounds([e(v,u) for u in range(N) if u!=v],9,9)
    for v in T:z.bounds([e(v,u) for u in T if u!=v],c-3,7)
    xy=[e(u,v) for u in X for v in Y];lo,hi=mx_bounds(c)
    if spec['kind']=='xy':lo,hi=spec['lo'],spec['hi']
    z.bounds(xy,lo,hi)
    if spec['kind']=='tdeg':
        z.bounds([e(T[0],u) for u in T[1:]],spec['lo'],spec['hi'])
    # Codegree <= global maximum c. Every nonedge has a common neighbor:
    # otherwise one endpoint together with the other's nine neighbors is I10.
    for i,j in pairs:
        if z.val(e(i,j)) is True:continue
        ws=[z.AND([e(i,k),e(j,k)]) for k in range(N) if k not in (i,j)]
        z.am(ws,c);z.add([e(i,j)]+ws)
    # Lex-max adjacency matrix over permutations within each label group.
    # Fix T labels entirely for catalog cores; don't impose T symmetry then.
    for C in [S,X,Y]+([] if spec['kind']=='core' else [T]):
        for i,j in zip(C,C[1:]):
            ks=[k for k in range(N) if k not in (i,j)]
            z.lex([e(i,k) for k in ks],[e(j,k) for k in ks])
    # For B subset of a root's nine independent neighbors, all vertices
    # in H missing A\B, together with B, have alpha<=|B|.
    # Therefore |H_B|<=R(3,|B|+1)-1-|B|.
    if hall:
        hcap=[0,1,3,5,9,12,16,20]
        for rt,nb in [(0,A),(1,B)]:
            H=[v for v in range(N) if v!=rt and v not in nb]
            for k in range(0,8):
                for sub in itertools.combinations(nb,k):
                    Q=set(sub);omit=[u for u in nb if u not in Q]
                    w=[z.AND([-e(u,v) for u in omit]) for v in H]
                    z.am(w,hcap[k])
                    if k==2:
                        # Any three such vertices must have an internal edge.
                        alive=[(v,l) for v,l in zip(H,w) if z.val(l) is not False]
                        for (u,a),(v,b),(t,d) in itertools.combinations(alive,3):
                            z.add([-a,-b,-d,e(u,v),e(u,t),e(v,t)])
    return z.f
def cut(s):
    assert len(s)==10 and len(set(s))==10 and min(s)>=0 and max(s)<40
    return [e(i,j) for i,j in itertools.combinations(sorted(s),2)]
def graph(model):
    yes={x for x in model if x>0};a=[0]*N
    for (i,j),x in edge.items():
        if x in yes:a[i]|=1<<j;a[j]|=1<<i
    return a
def save(p,obj):
    tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(obj,indent=2)+'\n');tmp.replace(p)
def sha(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''):h.update(b)
    return h.hexdigest()
def proof(f,out,seconds):
    cnf=out/'leaf.cnf';f.to_file(str(cnf));p=out/'leaf.drat'
    ret={'certificate':'NOT_VERIFIED','cnf_sha256':sha(cnf)}
    def cap():resource.setrlimit(resource.RLIMIT_FSIZE,(768*1024**2,768*1024**2))
    try:
        with open(out/'kissat.log','w') as log:
            r=subprocess.run(['kissat',str(cnf),str(p)],stdout=log,stderr=subprocess.STDOUT,timeout=seconds,preexec_fn=cap)
        ret['kissat_exit']=r.returncode
        if r.returncode==20:
            with open(out/'drat-trim.log','w') as log:
                v=subprocess.run(['drat-trim',str(cnf),str(p)],stdout=log,stderr=subprocess.STDOUT,timeout=seconds)
            if v.returncode==0 and 's VERIFIED' in (out/'drat-trim.log').read_text(errors='replace'):
                ret.update(certificate='VERIFIED_UNSAT',proof_sha256=sha(p))
                with open(p,'rb') as fi,gzip.open(out/'leaf.drat.gz','wb',compresslevel=1) as fo:shutil.copyfileobj(fi,fo)
        if ret['certificate']!='VERIFIED_UNSAT':cnf.unlink(missing_ok=True)
    except (OSError,subprocess.TimeoutExpired) as ex:
        ret['replay_error']=str(ex);cnf.unlink(missing_ok=True)
    finally:p.unlink(missing_ok=True)
    return ret
def verify_model(g,c,spec):
    S,X,Y,T=groups(c)
    assert all(x.bit_count()==9 for x in g)
    assert all(not(g[i]&g[j]) for i,j in pairs if g[i]>>j&1)
    assert not(g[0]>>1&1) and (g[0]&g[1]).bit_count()==c
    assert max((g[i]&g[j]).bit_count() for i,j in pairs)==c
    m=sum(g[i]>>j&1 for i in X for j in Y)
    assert mx_bounds(c)[0]<=m<=mx_bounds(c)[1]
    if spec['kind']=='xy':assert spec['lo']<=m<=spec['hi']
    elif spec['kind']=='tdeg':assert spec['lo']<=sum(g[T[0]]>>u&1 for u in T[1:])<=spec['hi']
    elif spec['kind']=='core':
        a=decode(spec['core']);assert all((g[T[i]]>>T[j]&1)==(a[i]>>j&1) for i,j in itertools.combinations(range(27),2))
def run(c,spec,out,seconds,proof_seconds,cap):
    out.mkdir(parents=True,exist_ok=True)
    f=formula(c,spec);rng=random.Random(310900+c*100+spec.get('lo',spec.get('idx',0)))
    S,X,Y,T=groups(c);H0=[1]+Y+T;H1=[0]+X+T
    assert len(H0)==len(H1)==30
    report=dict(c=c,spec=spec,status='OPEN',base_vars=f.nv,base_clauses=len(f.clauses),models=0,cuts=0,solver='cadical195')
    save(out/'result.json',report);print(json.dumps(report),flush=True)
    seen=set();start=time.monotonic()
    with Solver(name='cadical195',bootstrap_with=f.clauses) as sol,open(out/'cuts.jsonl','w',buffering=1) as fp:
        while time.monotonic()-start<seconds and len(seen)<cap:
            sol.conf_budget(50000);st=sol.solve_limited()
            if st is None:continue
            if st is False:report['status']='UNSAT_PENDING_REPLAY';break
            g=graph(sol.get_model());verify_model(g,c,spec);report['models']+=1
            # Fast structural separation: I8 in the common antineighborhood,
            # I9 in either root's antineighborhood, then general I10 search.
            bad=set()
            for verts,k,prefix in [(T,8,(0,1)),(H0,9,(0,)),(H1,9,(1,)),(range(N),10,())]:
                for s in independent(g,verts,k,512,rng):bad.add(tuple(sorted(prefix+s)))
            if not bad:
                # Independent, unbounded existence check in canonical order.
                assert not list(independent(g,range(N),10,1))
                (out/'witness.txt').write_text(''.join(''.join(str(g[i]>>j&1) for j in range(N))+'\n' for i in range(N)))
                report['status']='WITNESS_PENDING_INDEPENDENT_REPLAY';break
            for s in sorted(bad):
                assert s not in seen and all(not(g[i]>>j&1) for i,j in itertools.combinations(s,2))
                seen.add(s);cl=cut(s);sol.add_clause(cl);f.append(cl);fp.write(json.dumps(s)+'\n')
            report['cuts']=len(seen)
            if report['models']%10==0:save(out/'result.json',report);print(json.dumps(report),flush=True)
    if report['status']=='UNSAT_PENDING_REPLAY':
        report.update(proof(f,out,proof_seconds))
        report['status']='CERTIFIED_UNSAT' if report['certificate']=='VERIFIED_UNSAT' else 'OPEN_UNCERTIFIED_UNSAT'
    report['seconds']=time.monotonic()-start;save(out/'result.json',report);print(json.dumps(report),flush=True)
def selftest():
    for c in range(3,8):
        lo,hi=mx_bounds(c);ss=shards(c)
        if c!=7:assert [v for x in ss for v in range(x['lo'],x['hi']+1)]==list(range(lo,hi+1))
        else:assert [x['lo'] for x in ss]==[4,5,6,7] and lo==hi==4
    # Truth tables for signed conjunction and lex comparison.
    for n in range(1,5):
        z=Enc();xs=[i+1 for i in range(n)];p=z.AND(xs)
        with Solver(name='cadical195',bootstrap_with=z.f.clauses) as s:
            for b in itertools.product((0,1),repeat=n):
                ass=[x if v else -x for x,v in zip(xs,b)]
                assert s.solve(assumptions=ass+[p])==all(b)
                assert s.solve(assumptions=ass+[-p])==(not all(b))
        z=Enc();x=list(range(1,n+1));y=list(range(n+1,2*n+1));z.lex(x,y)
        with Solver(name='cadical195',bootstrap_with=z.f.clauses) as s:
            for b in itertools.product((0,1),repeat=2*n):
                ass=[i+1 if v else -(i+1) for i,v in enumerate(b)]
                assert s.solve(assumptions=ass)==(b[:n]>=b[n:])
    print('PASS: exhaustive split coverage, conjunction and lex truth tables',flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--selftest',action='store_true')
    p.add_argument('--c',type=int);p.add_argument('--spec');p.add_argument('--out');p.add_argument('--seconds',type=int,default=12600);p.add_argument('--proof-seconds',type=int,default=600);p.add_argument('--cut-cap',type=int,default=1000000)
    a=p.parse_args()
    if a.selftest:selftest()
    else:run(a.c,json.loads(a.spec),Path(a.out),a.seconds,a.proof_seconds,a.cut_cap)
