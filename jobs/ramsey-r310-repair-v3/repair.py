#!/usr/bin/env python3
"""Proof-producing exact repair and symmetry-normalized global search.
Every UNSAT certificate applies only to the explicitly stated branch.
All generated independent-set cuts are necessary original Ramsey clauses."""
import argparse, gzip, itertools, json, random, resource, shutil, subprocess, sys, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ramsey-r310-dag-v2'))
from solve import N,pairs,edge,e,bits,independent,graph,cut,save,digest
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver

class Encoding:
    def __init__(self):
        self.f=CNF();self.pool=IDPool(start_from=781)
    def var(self):return self.pool.id()
    def add(self,c):self.f.append(c)
    def am(self,xs,k):
        if k<0:self.add([])
        elif k<len(xs):self.f.extend(CardEnc.atmost(lits=xs,bound=k,vpool=self.pool,encoding=EncType.seqcounter).clauses)
    def al(self,xs,k):
        if k>len(xs):self.add([])
        elif k>0:self.f.extend(CardEnc.atleast(lits=xs,bound=k,vpool=self.pool,encoding=EncType.seqcounter).clauses)
    def addbits(self,x,y):
        # Exact binary adder, no unchecked pseudo-Boolean solver.
        out=[];carry=None
        for i in range(max(len(x),len(y))):
            ins=[a[i] for a in (x,y) if i<len(a)]
            if carry is not None:ins.append(carry)
            if len(ins)==1:out.append(ins[0]);carry=None;continue
            z=self.var();c=self.var()
            for b in itertools.product((0,1),repeat=len(ins)):
                premise=[-v if v1 else v for v,v1 in zip(ins,b)]
                s=sum(b)
                self.add(premise+[z if s%2 else -z]);self.add(premise+[c if s>=2 else -c])
            out.append(z);carry=c
        if carry is not None:out.append(carry)
        return out
    def sum_bits(self,xs):
        level=[[x] for x in xs]
        while len(level)>1:
            level=[self.addbits(level[i],level[i+1]) if i+1<len(level) else level[i] for i in range(0,len(level),2)]
        return level[0] if level else []
    def bound_bits(self,b,lo,hi):
        # For each bit differing from constant, forbid the wrong lex direction.
        for k in reversed(range(len(b))):
            up=[-b[j] if (hi>>j)&1 else b[j] for j in range(k+1,len(b))]
            dn=[-b[j] if (lo>>j)&1 else b[j] for j in range(k+1,len(b))]
            if not (hi>>k)&1:self.add(up+[-b[k]])
            if (lo>>k)&1:self.add(dn+[b[k]])
    def range(self,xs,lo,hi):
        if lo>len(xs) or hi<0 or lo>hi:self.add([]);return
        self.bound_bits(self.sum_bits(xs),max(0,lo),min(len(xs),hi))
    def lex_ge(self,x,y):
        p=None
        for a,b in zip(x,y):
            pre=[] if p is None else [-p]
            self.add(pre+[a,-b])
            z=self.var()
            # z iff prefix equal through this position.
            if p is not None:self.add([-z,p])
            self.add([-z,-a,b]);self.add([-z,a,-b])
            self.add(pre+[-a,-b,z]);self.add(pre+[a,b,z])
            p=z
    def triangles(self):
        for i,j,k in itertools.combinations(range(N),3):self.add([-e(i,j),-e(i,k),-e(j,k)])

def read_seed():
    s=(HERE/'seed31002.txt').read_text().splitlines()
    assert len(s)==40 and all(len(x)==40 and set(x)<=set('01') for x in s)
    a=[sum(1<<j for j,c in enumerate(row) if c=='1') for row in s]
    assert all(a[i].bit_count()==9 and not(a[i]>>i&1) for i in range(N))
    assert all((a[i]>>j&1)==(a[j]>>i&1) for i,j in pairs)
    assert all(not(a[i]&a[j]) for i,j in pairs if a[i]>>j&1)
    assert len(list(independent(a,10)))==10
    return a

def local_base(k,l):
    z=Encoding();a=read_seed();z.triangles()
    for i in range(N):z.am([e(i,j) for j in range(N) if j!=i],9)
    adds=[e(i,j) for i,j in pairs if not(a[i]>>j&1)]
    dels=[-e(i,j) for i,j in pairs if a[i]>>j&1]
    z.am(adds,k);z.am(dels,l)
    return z.f,a

def global_base(d,q):
    assert 5<=d<=9 and 5<=q<=9 and (d!=9 or q==9)
    z=Encoding();A=list(range(1,d+1));H=list(range(d+1,N))
    for i in range(1,N):z.add([e(0,i) if i in A else -e(0,i)])
    for i,j in itertools.combinations(A,2):z.add([-e(i,j)])
    z.triangles()
    for i,j in pairs:
        if i==0:continue
        cs=[]
        for k in range(N):
            if k in (i,j):continue
            c=z.var();cs.append(c);z.add([-c,e(i,k)]);z.add([-c,e(j,k)])
        z.add([e(i,j)]+cs)
    for i in range(N):
        xs=[e(i,j) for j in range(N) if j!=i]
        lo=9 if d==9 else q if i in A else 5;hi=9
        if d==5 and (i in H or (q==5 and i in A and i!=1)):lo=max(lo,7)
        if d==6 and i!=1:lo=max(lo,6)
        if i==0:lo=hi=d
        if i==1:lo=hi=q
        z.am(xs,hi);z.al(xs,lo)
    for i in H:
        z.al([e(i,j) for j in H if i!=j],11-d)
        z.add([e(i,j) for j in A])
    for i,j in zip(H,H[1:]):z.lex_ge([e(u,i) for u in A],[e(u,j) for u in A])
    for t,i in enumerate(H):z.add([e(1,i) if t<q-1 else -e(1,i)])
    hs=[e(i,j) for i,j in itertools.combinations(H,2)]
    emin={5:129,6:118,7:104,8:95,9:86}[d]
    z.range(hs,99 if d==9 else emin,180-9*d)
    z.range(list(edge.values()),159,180)
    return z.f

def encoding_selftest():
    # Exhaustively check all small assignments for signed cardinality and lex.
    for n in range(1,8):
        for lo in range(n+1):
            for hi in range(lo,n+1):
                z=Encoding();xs=[(-i if i%2 else i) for i in range(1,n+1)];z.range(xs,lo,hi)
                with Solver(name='cadical195',bootstrap_with=z.f.clauses) as s:
                    for b in itertools.product((0,1),repeat=n):
                        ass=[x if v else -x for x,v in zip(xs,b)]
                        assert s.solve(assumptions=ass)==(lo<=sum(b)<=hi)
    for n in range(1,5):
        z=Encoding();x=list(range(1,n+1));y=list(range(n+1,2*n+1));z.lex_ge(x,y)
        with Solver(name='cadical195',bootstrap_with=z.f.clauses) as s:
            for b in itertools.product((0,1),repeat=2*n):
                assert s.solve(assumptions=[i+1 if v else -(i+1) for i,v in enumerate(b)])==(b[:n]>=b[n:])
    print('PASS: signed exact adder ranges and lex order exhaustive truth tables',flush=True)

def proof(f,out,seconds):
    cnf=out/'leaf.cnf';f.to_file(str(cnf));p=out/'leaf.drat'
    ret={'certificate':'NOT_VERIFIED','cnf_sha256':digest(cnf)}
    def cap():resource.setrlimit(resource.RLIMIT_FSIZE,(768*1024**2,768*1024**2))
    try:
        with open(out/'kissat.log','w') as log:
            r=subprocess.run(['kissat',str(cnf),str(p)],stdout=log,stderr=subprocess.STDOUT,timeout=seconds,preexec_fn=cap)
        ret['kissat_exit']=r.returncode
        if r.returncode==20:
            with open(out/'drat-trim.log','w') as log:
                v=subprocess.run(['drat-trim',str(cnf),str(p)],stdout=log,stderr=subprocess.STDOUT,timeout=seconds)
            if v.returncode==0 and 's VERIFIED' in (out/'drat-trim.log').read_text(errors='replace'):
                ret.update(certificate='VERIFIED_UNSAT',proof_sha256=digest(p))
                with open(p,'rb') as fi,gzip.open(out/'leaf.drat.gz','wb',compresslevel=1) as fo:shutil.copyfileobj(fi,fo)
        if ret['certificate']!='VERIFIED_UNSAT':cnf.unlink(missing_ok=True)
    except (OSError,subprocess.TimeoutExpired) as ex:
        ret['replay_error']=str(ex);cnf.unlink(missing_ok=True)
    finally:p.unlink(missing_ok=True)
    return ret

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--selftest',action='store_true')
    p.add_argument('--mode',choices=['local','global'],default='local');p.add_argument('--k',type=int,default=4);p.add_argument('--l',type=int,default=8)
    p.add_argument('--d',type=int,default=5);p.add_argument('--q',type=int,default=5)
    p.add_argument('--near',default='near.txt');p.add_argument('--reuse');p.add_argument('--reuse-limit',type=int,default=200000)
    p.add_argument('--seconds',type=int,default=900);p.add_argument('--proof-seconds',type=int,default=300);p.add_argument('--out',default='out')
    a=p.parse_args()
    if a.selftest:encoding_selftest();return
    out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
    if a.mode=='local':
        f,seed=local_base(a.k,a.l);label=f'LOCAL-{a.k}-{a.l}'
    else:
        f=global_base(a.d,a.q);seed=None;label=f'D{a.d}-N{a.q}'
    report={'branch':label,'status':'OPEN','base_vars':f.nv,'base_clauses':len(f.clauses),'models':0,'cuts':0}
    seen=set();rng=random.Random(20261126+100*a.k+a.l+1000*a.d+a.q);order=list(range(N))
    start=time.monotonic()
    with open(out/'cuts.jsonl','w',buffering=1) as fo:
        def initial(s):
            s=tuple(sorted(s))
            if s not in seen:
                f.append(cut(s));seen.add(s);fo.write(json.dumps(s)+'\n')
        if seed is not None:
            counts={}
            for line in Path(a.near).read_text().splitlines():
                v=list(map(int,line.split()));cost,s=v[0],v[1:]
                assert cost==sum(seed[i]>>j&1 for i,j in itertools.combinations(s,2))
                initial(s);counts[cost]=counts.get(cost,0)+1
            assert counts.get(0)==10 and counts.get(1)==18015
            report['near_counts']=counts
        else:
            A=range(1,a.d+1);H=range(a.d+1,N)
            # Deterministic original I10 clauses with all A vertices and up to 4 H.
            if 10-a.d<=4:
                for s in itertools.combinations(H,10-a.d):initial(tuple(A)+s)
            # Reuse cuts produced by the identical labeled global leaf.
            if a.reuse and Path(a.reuse).exists():
                with open(a.reuse) as fp:
                    for i,line in enumerate(fp):
                        if i>=a.reuse_limit:break
                        initial(json.loads(line))
            report['reused_and_seed_cuts']=len(seen)
        report['cuts']=len(seen);save(out/'result.json',report);print(json.dumps(report),flush=True)
        with Solver(name='cadical195',bootstrap_with=f.clauses) as sol:
            if seed is not None:sol.set_phases([e(i,j) if seed[i]>>j&1 else -e(i,j) for i,j in pairs])
            while time.monotonic()-start<a.seconds:
                sol.conf_budget(50000);st=sol.solve_limited()
                if st is None:continue
                if st is False:report['status']='UNSAT_PENDING_REPLAY';break
                g=graph(sol.get_model());report['models']+=1
                assert all(not(g[i]&g[j]) for i,j in pairs if g[i]>>j&1)
                if seed is not None:
                    add=sum((g[i]&~seed[i]).bit_count() for i in range(N))//2
                    delete=sum((seed[i]&~g[i]).bit_count() for i in range(N))//2
                    assert add<=a.k and delete<=a.l
                rng.shuffle(order);bad=list(independent(g,10,512,order))
                if not bad:
                    (out/'witness.txt').write_text(''.join(''.join(str(g[i]>>j&1) for j in range(N))+'\n' for i in range(N)))
                    report['status']='WITNESS_PENDING_INDEPENDENT_REPLAY'
                    if seed is not None:report.update(added=add,deleted=delete)
                    break
                for s in bad:
                    assert s not in seen
                    c=cut(s);sol.add_clause(c);f.append(c);seen.add(s);fo.write(json.dumps(s)+'\n')
                report['cuts']=len(seen)
                if report['models']%25==0:save(out/'result.json',report);print(json.dumps(report),flush=True)
    if report['status']=='UNSAT_PENDING_REPLAY':
        # Same base plus independently rechecked serialized original cuts, not
        # incremental solver's learned clauses, is the standalone certificate input.
        report.update(proof(f,out,a.proof_seconds))
        report['status']='CERTIFIED_UNSAT' if report['certificate']=='VERIFIED_UNSAT' else 'OPEN_UNCERTIFIED_UNSAT'
    report['seconds']=time.monotonic()-start;save(out/'result.json',report);print(json.dumps(report),flush=True)
if __name__=='__main__':main()
