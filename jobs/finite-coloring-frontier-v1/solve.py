#!/usr/bin/env python3
"""Finite hypergraph coloring, proof-first SAT, and exact restricted repair."""
import argparse, itertools, json, hashlib, gzip, shutil, subprocess, time, re, resource
from pathlib import Path
ROOT=Path(__file__).resolve().parent
KNOWN={'vdw':[(2,9),(3,27),(4,76)],'schur':[(1,2),(2,5),(3,14),(4,45),(5,161)]}
A='1214532151415455221412131223442151413435231512441225413135322515141312233421314255522313123452214421513353131415524432213122432215151435332141216142453215141545512141216362141216145641516161626666141316564651614166626616161626666166616666666666666636616166666666666666666666666666666666666366666661666666161666666261666666266616666564656131416666261616156465416121412636121412156451415123542416121412335141515122342213122344255141313523151244122543213132255524131243322131415152235313145221442151325343141512443221312141225545141512354121'
B='1214532151415455221412131223442151413435231512441225413135322515141312233421314255522313123452214421513353131415524432213122432215151435332141216142453215141546512141216362141216145241516161626666141316564651616666626616661626664166656666661666666636656666666366666666666666616666661666666366666661665666561654666261616166266614151524656135416666261516151425456121412636121412155451415123542416121412335341515122343233122344255541313533151244122543213132255524131243322131415152235313145221442151325343145512443221312141225545143512354121'
def seed(kind,which='a'):
    if kind=='schur':
        s=A if which=='a' else B
        assert hashlib.sha256((s+'\n').encode()).hexdigest()=={'a':'9e149c007b778655afd199685ebcc76260604a44f4c322d8aa9a1d96afb71d20','b':'00824bdd056da8543aa66878d3e1a86b123c7a814c701978e8d3c169226c4f58'}[which]
        return [int(x)-1 for x in s]
    f={0:0,**{pow(3,i,17):pow(3,i,5)%5 for i in range(16)}}
    return [(3*j+f[j%17])%5 for j in range(1,171)]
def edges(kind,n):
    if kind=='vdw':
        return [(a,a+d,a+2*d) for d in range(1,(n-1)//2+1) for a in range(1,n-2*d+1)]
    return [tuple(sorted({a,b,a+b})) for a in range(1,n//2+1) for b in range(a,n-a+1)]
def verify(kind,w,k):
    if not w or not all(0<=x<k for x in w):return False
    n=len(w)
    for a in range(1,n+1):
        for b in range(a+(kind=='vdw'),n+1):
            c=2*b-a if kind=='vdw' else a+b
            if c<=n and w[a-1]==w[b-1]==w[c-1]:return False
    return True
def canonical(w):
    p={};return tuple(p.setdefault(x,len(p)) for x in w)
def prefixes(kind):
    k=5 if kind=='vdw' else 6
    return sorted({canonical(w) for w in itertools.product(range(k),repeat=3) if verify(kind,w,k)})
def copies(kind,n,s):
    if kind=='vdw':
        for d in range(1,(n-1)//(s-1)+1):
            for a in range(1,n-(s-1)*d+1):yield tuple(a+j*d for j in range(s))
    else:
        for d in range(1,n//s+1):yield tuple(d*j for j in range(1,s+1))
def formula(kind,n,k,mode='windows',prefix=(),repair=None):
    def v(i,c):return (i-1)*k+c+1
    nv=n*k;cs=[]
    for i in range(1,n+1):
        cs.append([v(i,c) for c in range(k)])
        cs.extend([-v(i,a),-v(i,b)] for a,b in itertools.combinations(range(k),2))
    for e in edges(kind,n):
        cs.extend([-v(i,c) for i in e] for c in range(k))
    if repair is not None:
        from pysat.card import CardEnc,EncType
        w,c,b=repair;assert len(w)==n-1 and verify(kind,w,k) and not prefix
        cs.append([v(n,c)])
        h=CardEnc.atmost(lits=[-v(i,c0) for i,c0 in enumerate(w,1)],bound=b,top_id=nv,encoding=EncType.seqcounter)
        nv=max(nv,h.nv);cs.extend(h.clauses)
    elif mode=='baseline':
        for i in range(1,n+1):
            for c in range(1,k):cs.append([-v(i,c)]+[v(j,c-1) for j in range(1,i)])
    else:
        def seen(i,c):return n*k+(i-1)*k+c+1
        nv=2*n*k
        for i in range(1,n+1):
            for c in range(k):
                t=seen(i,c);u=v(i,c)
                if i==1:cs.extend([[-u,t],[-t,u]])
                else:
                    prev=seen(i-1,c);cs.extend([[-u,t],[-prev,t],[-t,u,prev]])
                if c:cs.append([-u,seen(i-1,c-1)] if i>1 else [-u])
        if mode=='windows':
            for t,s in KNOWN[kind]:
                if t>=k:continue
                for a in copies(kind,n,s):
                    for outside in itertools.combinations(range(k),k-t):
                        cs.append([v(i,c) for i in a for c in outside])
    cs.extend([[v(i,c)] for i,c in enumerate(prefix,1)])
    assert max(abs(l) for cl in cs for l in cl)<=nv
    return nv,cs
def digest(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for chunk in iter(lambda:f.read(1<<20),b''):h.update(chunk)
    return h.hexdigest()
def dump(path,obj):
    tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(obj,indent=2)+'\n');tmp.replace(path)
def cnfwrite(path,nv,cs):
    with open(path,'w') as f:
        f.write(f'p cnf {nv} {len(cs)}\n')
        for cl in cs:f.write(' '.join(map(str,cl))+' 0\n')
def selftest():
    assert prefixes('vdw')==[(0,0,1),(0,1,0),(0,1,1),(0,1,2)]
    assert prefixes('schur')==[(0,1,0),(0,1,1),(0,1,2)]
    assert all(verify('vdw',seed('vdw'),5) for _ in [0])
    assert all(len(seed('schur',x))==538 and verify('schur',seed('schur',x),6) for x in ('a','b'))
    # Exhaustive semantic truth table for primary assignments with canonical labels.
    for kind,n,k in [('vdw',8,3),('vdw',9,3),('schur',6,3)]:
        for mode in ('baseline','prefix','windows'):
            nv,cs=formula(kind,n,k,mode)
            for w in itertools.product(range(k),repeat=n):
                if canonical(w)!=w:continue
                true={i*k+c+1 for i,c in enumerate(w)}
                if mode!='baseline':
                    true|={n*k+i*k+c+1 for i in range(n) for c in set(w[:i+1])}
                got=all(any((l>0)==(abs(l) in true) for l in cl) for cl in cs)
                assert got==verify(kind,w,k),(kind,mode,w)
    print('SELFTEST PASS: both seed families, 7 complete canonical first-three prefixes, small exhaustive semantic encoding controls',flush=True)
def run(a):
    kind=a.kind;n=171 if kind=='vdw' else 539;k=5 if kind=='vdw' else 6
    out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
    prefix=tuple(map(int,a.prefix)) if a.prefix else ()
    repair=None
    if a.radius is not None:
        w=seed(kind,a.seed);repair=(w,a.color,a.radius)
    else:assert prefix in prefixes(kind)
    nv,cs=formula(kind,n,k,a.mode,prefix,repair)
    path=out/'instance.cnf';cnfwrite(path,nv,cs)
    r=dict(kind=kind,n=n,k=k,scope='RESTRICTED_REPAIR' if repair else 'GLOBAL_PREFIX_CASE',prefix=a.prefix,mode=a.mode,color=a.color,radius=a.radius,seed=a.seed if repair else None,variables=nv,clauses=len(cs),cnf_sha256=digest(path),status='OPEN')
    dump(out/'result.json',r);start=time.monotonic()
    proof=out/'proof.drat'
    def cap():resource.setrlimit(resource.RLIMIT_FSIZE,(512*1024**2,512*1024**2))
    try:
        with open(out/'kissat.log','w') as f:
            ret=subprocess.run(['kissat',str(path),str(proof)],stdout=f,stderr=subprocess.STDOUT,timeout=a.seconds,preexec_fn=cap)
        r['exit']=ret.returncode
    except (OSError,subprocess.TimeoutExpired) as e:
        r['error']=str(e);ret=None
    r['solve_seconds']=round(time.monotonic()-start,3)
    try:
        if ret is not None and ret.returncode==10:
            log=(out/'kissat.log').read_text(errors='replace')
            vs={int(v) for line in log.splitlines() if line.startswith('v ') for v in line[2:].split() if v!='0'}
            w=[]
            for i in range(n):
                c=[j for j in range(k) if i*k+j+1 in vs];assert len(c)==1;w+=c
            assert verify(kind,w,k)
            if repair:assert w[-1]==a.color and sum(x!=y for x,y in zip(w,repair[0]))<=a.radius
            else:assert tuple(w[:3])==prefix
            (out/'witness.word').write_text(''.join(map(str,w))+'\n')
            r.update(status='VERIFIED_WITNESS',witness_sha256=digest(out/'witness.word'))
        elif ret is not None and ret.returncode==20:
            r['status']='UNSAT_UNCERTIFIED';start=time.monotonic()
            with open(out/'drat-trim.log','w') as f:
                check=subprocess.run(['drat-trim',str(path),str(proof)],stdout=f,stderr=subprocess.STDOUT,timeout=a.proof_seconds)
            r['check_seconds']=round(time.monotonic()-start,3)
            if check.returncode==0 and 's VERIFIED' in (out/'drat-trim.log').read_text(errors='replace'):
                r.update(status='CERTIFIED_UNSAT',proof_sha256=digest(proof),proof_bytes=proof.stat().st_size)
                with open(proof,'rb') as fi,gzip.open(out/'proof.drat.gz','wb',compresslevel=1) as fo:shutil.copyfileobj(fi,fo)
    except (OSError,subprocess.TimeoutExpired,AssertionError) as e:
        r['verification_error']=str(e)
        if r['status']=='VERIFIED_WITNESS':r['status']='OPEN'
    finally:proof.unlink(missing_ok=True)
    dump(out/'result.json',r);print(json.dumps(r),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--selftest',action='store_true');p.add_argument('--kind',choices=['vdw','schur']);p.add_argument('--prefix',default='');p.add_argument('--mode',choices=['baseline','prefix','windows'],default='windows');p.add_argument('--radius',type=int);p.add_argument('--color',type=int);p.add_argument('--seed',choices=['a','b'],default='a');p.add_argument('--seconds',type=int,default=180);p.add_argument('--proof-seconds',type=int,default=120);p.add_argument('--out',default='out')
    a=p.parse_args()
    if a.selftest:selftest()
    else:run(a)
