#!/usr/bin/env python3
"""Exact R(5,5) root-cover and fixed-core gluing. Proof-first, bounded."""
import argparse,itertools,math,json,hashlib,time,subprocess,gzip,shutil,resource
from pathlib import Path
E={18:85,19:92,20:100,21:107,22:114,23:122,24:132}
L={18:50,19:57,20:68,21:77,22:88,23:101,24:116}
C=math.comb
HERE=Path(__file__).resolve().parent
def decode(s):
    s=s.strip();assert 1<=ord(s[0])-63<=62
    n=ord(s[0])-63;assert len(s)==1+(C(n,2)+5)//6
    a=[0]*n;k=0
    for j in range(n):
        for i in range(j):
            if ((ord(s[1+k//6])-63)>>(5-k%6))&1:a[i]|=1<<j;a[j]|=1<<i
            k+=1
    return a
def complement(a):
    m=(1<<len(a))-1
    return [(m^(1<<i))^b for i,b in enumerate(a)]
def bits(x):
    while x:
        b=x&-x;yield b.bit_length()-1;x^=b
def clique(a,k,p=None):
    if k==0:return True
    if p is None:p=(1<<len(a))-1
    while p.bit_count()>=k:
        b=p&-p;p^=b;i=b.bit_length()-1
        if clique(a,k-1,p&a[i]):return True
    return False
def verify(a,s=5,t=5):
    n=len(a);assert all(not ((b>>i)&1) and b>>n==0 for i,b in enumerate(a))
    assert all(((a[i]>>j)&1)==((a[j]>>i)&1) for i,j in itertools.combinations(range(n),2))
    return not clique(a,s) and not clique(complement(a),t)
def nedges(a):return sum(b.bit_count() for b in a)//2
def threshold(n,d):
    h=n-1-d
    return C(h,2)-d*(n-2*d)//2
def cover():
    rows=[]
    for n in (43,44,45):
        for d in range(n-25,(n-1)//2+1):
            h=n-1-d;z=threshold(n,d);pairs=[];triples=0
            for a in range(L[d],E[d]+1):
                for b in range(L[h],E[h]+1):
                    if a+b<z:continue
                    lo=max(0,d*(n-26)-2*a,h*(n-25)-2*(C(h,2)-b))
                    hi=min(d*h,d*23-2*a,h*24-2*(C(h,2)-b))
                    if lo<=hi:pairs.append([a,b]);triples+=hi-lo+1
            rows.append(dict(n=n,d=d,h=h,threshold=z,min_A=min(a for a,b in pairs),min_B=min(b for a,b in pairs),pairs=len(pairs),triples=triples))
    return rows
def control():
    # Exhaustively verify doubled excess sum and complement invariance on
    # every labeled simple graph of order <=5 (proof in README).
    for n in range(1,6):
        es=list(itertools.combinations(range(n),2))
        for mask in range(1<<len(es)):
            g=[0]*n
            for j,(u,v) in enumerate(es):
                if mask>>j&1:g[u]|=1<<v;g[v]|=1<<u
            def excess(a,i):
                nb=list(bits(a[i]));h=[j for j in range(n) if j!=i and not(a[i]>>j&1)]
                ea=sum(a[u]>>v&1 for u,v in itertools.combinations(nb,2))
                eh=sum(a[u]>>v&1 for u,v in itertools.combinations(h,2))
                return 2*(eh-ea)-len(nb)*(n-2*len(nb))
            vals=[excess(g,i) for i in range(n)]
            assert sum(vals)==0 and vals==[excess(complement(g),i) for i in range(n)]
    g=decode((HERE/'seed42.g6').read_text());assert len(g)==42 and nedges(g)==425 and verify(g)
    rows=cover();assert [(x['d'],x['pairs'],x['triples']) for x in rows if x['n']==43]==[(18,15,1595),(19,45,5035),(20,105,12133),(21,120,14000)]
    print(json.dumps(dict(status='CONTROLS_PASS',seed42_edges=425,cover=rows)),flush=True)
def select_catalog(path,out):
    expected={128:843,129:147,130:32,131:3,132:2}
    counts={x:0 for x in expected};selected=[];total=0;unique=set()
    with open(path) as f:
        for line in f:
            if not line.strip():continue
            s=line.strip();assert len(s)==47 and s[0]=='W'
            # graph6 payload: all 276 edge bits exactly fill 46 chars.
            m=sum((ord(x)-63).bit_count() for x in s[1:])
            total+=1
            if m in counts:
                assert s not in unique;unique.add(s);counts[m]+=1
                g=decode(s);assert len(g)==24 and nedges(g)==m and verify(g,4,5)
                if m>=131:selected.append((m,s))
    assert total==352366 and counts==expected
    selected.sort(key=lambda x:(-x[0],x[1]))
    assert len(selected)==5
    Path(out).write_text(json.dumps(dict(total=total,high_density_counts=counts,source_sha256=digest(path),cores=[dict(index=i,edges=m,graph6=s) for i,(m,s) in enumerate(selected)]),indent=2)+'\n')
    print(json.dumps(dict(status='CATALOG_COUNTS_AND_SELECTED_HIGH_DENSITY_GRAPHS_VERIFIED',total=total,counts=counts,pilot_cores=5)),flush=True)
def digest(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for x in iter(lambda:f.read(1<<20),b''):h.update(x)
    return h.hexdigest()
def encode(n,fixed,d,out):
    from pysat.card import CardEnc,EncType
    from pysat.formula import IDPool
    pairs=list(itertools.combinations(range(n),2))
    variables={e:i+1 for i,e in enumerate(pairs) if e not in fixed}
    # Compact unknown-edge numbering (rather than allocating fixed variables).
    variables={e:i+1 for i,e in enumerate(variables)}
    pool=IDPool(start_from=len(variables)+1)
    def project(es,positive):
        res=[]
        for e in es:
            if e in fixed:
                if bool(fixed[e])==positive:return None
            else:res.append(variables[e] if positive else -variables[e])
        return res
    count=0
    path=out/'instance.cnf';body=out/'clauses.tmp'
    with open(body,'w') as f:
        def emit(ls):
            nonlocal count
            f.write(' '.join(map(str,ls))+' 0\n');count+=1
        def card(es,positive,lo,hi):
            known=sum(bool(fixed[e])==positive for e in es if e in fixed)
            ls=[variables[e] if positive else -variables[e] for e in es if e not in fixed]
            lo-=known;hi-=known
            if lo>len(ls) or hi<0 or lo>hi:emit([]);return
            if lo>0:
                for cl in CardEnc.atleast(lits=ls,bound=lo,vpool=pool,encoding=EncType.seqcounter).clauses:emit(cl)
            if hi<len(ls):
                for cl in CardEnc.atmost(lits=ls,bound=hi,vpool=pool,encoding=EncType.seqcounter).clauses:emit(cl)
        for ss in itertools.combinations(range(n),5):
            es=list(itertools.combinations(ss,2))
            for sign in (False,True):
                cl=project(es,sign)
                if cl is not None:emit(cl)
        base_count=count
        for v in range(n):
            es=[tuple(sorted((v,j))) for j in range(n) if j!=v]
            card(es,True,n-25,24)
        if d is not None:
            A=list(range(1,d+1));B=list(range(d+1,n));h=len(B)
            ae=list(itertools.combinations(A,2));be=list(itertools.combinations(B,2))
            card(ae,True,max(L[d],threshold(n,d)-E[h]),E[d])
            card(be,False,max(L[h],threshold(n,d)-E[d]),E[h])
            # Sum a+b >= threshold, with mixed literals and fixed projection.
            known=sum(fixed[e] for e in ae if e in fixed)+sum(not fixed[e] for e in be if e in fixed)
            ls=[variables[e] for e in ae if e not in fixed]+[-variables[e] for e in be if e not in fixed]
            bound=threshold(n,d)-known
            if bound>len(ls):emit([])
            elif bound>0:
                for cl in CardEnc.atleast(lits=ls,bound=bound,vpool=pool,encoding=EncType.seqcounter).clauses:emit(cl)
            for group,sign in [(A,True),(B,False)]:
                for v in group:
                    card([tuple(sorted((v,j))) for j in group if j!=v],sign,len(group)-18,13)
    nv=max(pool.top,len(variables))
    with open(path,'wb') as f,open(body,'rb') as src:
        f.write(f'p cnf {nv} {count}\n'.encode());shutil.copyfileobj(src,f)
    body.unlink()
    return variables,dict(edge_variables=len(variables),cnf_variables=nv,clique_clauses=base_count,clauses=count,cnf_sha256=digest(path))
def run(a):
    n=43;out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
    fixed={};d=None;core=None
    if a.kind=='catalog':
        d=18;record=json.loads(Path(a.catalog).read_text())['cores'][a.index]
        g=decode(record['graph6']);assert len(g)==24 and verify(g,4,5) and nedges(g)==record['edges']
        core=record
        for j in range(1,n):fixed[0,j]=j<=d
        for i,j in itertools.combinations(range(24),2):fixed[d+1+i,d+1+j]=not(g[i]>>j&1)
    else:
        g=decode((HERE/'seed42.g6').read_text());assert verify(g)
        deleted=list(range(a.delete));keep=[i for i in range(42) if i not in deleted]
        core=dict(seed='McKay catalog first record',deleted=deleted,retained=len(keep))
        for i,j in itertools.combinations(range(len(keep)),2):fixed[i,j]=bool(g[keep[i]]>>keep[j]&1)
    start=time.monotonic();vs,m=encode(n,fixed,d,out)
    r=dict(kind=a.kind,n=n,core=core,scope='RESTRICTED_FIXED_CORE',root_degree=d,status='OPEN',build_seconds=round(time.monotonic()-start,3),**m)
    def save():
        (out/'result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
    save();cnf=out/'instance.cnf';pr=out/'proof.drat';start=time.monotonic()
    def cap():resource.setrlimit(resource.RLIMIT_FSIZE,(768*1024**2,768*1024**2))
    try:
        with open(out/'kissat.log','w') as log:
            k=subprocess.run(['kissat',str(cnf),str(pr)],stdout=log,stderr=subprocess.STDOUT,timeout=a.seconds,preexec_fn=cap)
        r['exit']=k.returncode;r['solve_seconds']=round(time.monotonic()-start,3)
        if k.returncode==10:
            pos={int(v) for line in (out/'kissat.log').read_text().splitlines() if line.startswith('v ') for v in line[2:].split() if v!='0'}
            G=[0]*n
            for i,j in itertools.combinations(range(n),2):
                if fixed.get((i,j),False) if (i,j) in fixed else vs[i,j] in pos:G[i]|=1<<j;G[j]|=1<<i
            assert verify(G)
            # Second, independent implementation for final acceptance.
            import networkx as nx
            gg=nx.Graph();gg.add_nodes_from(range(n));gg.add_edges_from((i,j) for i,j in itertools.combinations(range(n),2) if G[i]>>j&1)
            assert max(map(len,nx.find_cliques(gg)))<=4 and max(map(len,nx.find_cliques(nx.complement(gg))))<=4
            nx.write_graph6(gg,out/'witness43.g6',header=False);r['status']='VERIFIED_ORIGINAL_WITNESS';r['witness_sha256']=digest(out/'witness43.g6')
        elif k.returncode==20:
            r['status']='UNSAT_UNCERTIFIED';start=time.monotonic()
            with open(out/'drat-trim.log','w') as log:
                z=subprocess.run(['drat-trim',str(cnf),str(pr)],stdout=log,stderr=subprocess.STDOUT,timeout=a.proof_seconds)
            r['check_seconds']=round(time.monotonic()-start,3)
            if z.returncode==0 and 's VERIFIED' in (out/'drat-trim.log').read_text(errors='replace'):
                r.update(status='CERTIFIED_UNSAT_RESTRICTED_CORE',proof_sha256=digest(pr),proof_bytes=pr.stat().st_size)
                with open(pr,'rb') as fi,gzip.open(out/'proof.drat.gz','wb',compresslevel=1) as fo:shutil.copyfileobj(fi,fo)
    except (OSError,subprocess.TimeoutExpired,AssertionError) as ex:r['error']=str(ex)
    finally:pr.unlink(missing_ok=True)
    save()
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--control',action='store_true');p.add_argument('--select');p.add_argument('--kind',choices=['catalog','repair']);p.add_argument('--catalog');p.add_argument('--index',type=int,default=0);p.add_argument('--delete',type=int,default=7);p.add_argument('--seconds',type=int,default=240);p.add_argument('--proof-seconds',type=int,default=120);p.add_argument('--out',required=False,default='out')
    a=p.parse_args()
    if a.control:control()
    elif a.select:select_catalog(a.select,a.out)
    else:run(a)
