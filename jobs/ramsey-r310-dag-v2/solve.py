#!/usr/bin/env python3
import argparse,itertools,json,time,subprocess,resource,hashlib,random,gzip,shutil
from pathlib import Path
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
N=40
pairs=list(itertools.combinations(range(N),2))
edge={p:i+1 for i,p in enumerate(pairs)}
def e(i,j):return edge[tuple(sorted((i,j)))]
def bits(p):
    while p:
        x=p&-p;p^=x;yield x.bit_length()-1
def independent(a,k,limit=None,order=None):
    n=len(a);order=list(range(n)) if order is None else order
    inv={v:i for i,v in enumerate(order)}
    b=[sum(1<<inv[j] for j in bits(a[v])) for v in order];count=0
    def go(p,k,s):
        nonlocal count
        if limit is not None and count>=limit:return
        if k==0:
            count+=1;yield tuple(sorted(s));return
        while p.bit_count()>=k and (limit is None or count<limit):
            x=p&-p;p^=x;i=x.bit_length()-1
            yield from go(p&~b[i],k-1,s+[order[i]])
    yield from go((1<<n)-1,k,[])
def core_data():
    path=Path(__file__).resolve().parent.parent/'ramsey-r310-wave1'/'kalbfleisch35.g6'
    s=path.read_bytes().strip();assert s[0]-63==35 and len(s)==101
    a=[0]*35;k=0
    for j in range(35):
        for i in range(j):
            if ((s[1+k//6]-63)>>(5-k%6))&1:a[i]|=1<<j;a[j]|=1<<i
            k+=1
    assert all(x.bit_count()==8 for x in a)
    assert all(not(a[i]&a[j]) for i in range(35) for j in bits(a[i]))
    assert not list(independent(a,9,1))
    targets=[sum(1<<i for i in s) for s in independent(a,8)]
    rows=targets+[m for s in independent(a,7) if all(any(a[i]>>j&1 for i in s) for j in range(35) if j not in s) for m in [sum(1<<i for i in s)]]
    # Prove no smaller maximal independent sets as part of the compatibility argument.
    for k in range(1,7):
        assert all(any(all(not(a[i]>>j&1) for i in s) for j in range(35) if j not in s) for s in independent(a,k))
    assert len(rows)==3365 and len(targets)==3360
    miss=[]
    for s in rows:
        m=bytearray((len(targets)+7)//8)
        for i,t in enumerate(targets):
            if not s&t:m[i//8]|=1<<(i%8)
        miss.append(int.from_bytes(m,'little'))
    assert all(miss)
    adj=[0]*len(rows);count=0
    for i,mi in enumerate(miss):
        for j in range(i):
            if not mi&miss[j]:adj[i]|=1<<j;adj[j]|=1<<i;count+=1
    assert count==191100 and all(not(adj[i]&adj[j]) for i in range(len(adj)) for j in bits(adj[i]))
    return a,targets
def base(d,q,core):
    f=CNF();pool=IDPool(start_from=781)
    def am(xs,k,enc=EncType.seqcounter):
        if k<0:f.append([])
        elif k<len(xs):f.extend(CardEnc.atmost(lits=xs,bound=k,vpool=pool,encoding=enc).clauses)
    def al(xs,k,enc=EncType.seqcounter):
        if k>len(xs):f.append([])
        elif k>0:am([-x for x in xs],len(xs)-k,enc)
    if core:
        a,targets=core_data()
        for i,j in itertools.combinations(range(35),2):f.append([e(i,j) if a[i]>>j&1 else -e(i,j)])
        for i,j in itertools.combinations(range(35,40),2):f.append([e(i,j) if j-i in (1,4) else -e(i,j)])
        for v in range(35):am([e(v,u) for u in range(35,40)],1)
        for u in range(35,40):
            for i,j in itertools.combinations(range(35),2):
                if a[i]>>j&1:f.append([-e(u,i),-e(u,j)])
            am([e(u,i) for i in range(35)],7)
        for u,v in itertools.combinations(range(35,40),2):
            if v-u not in (1,4):
                for t in targets:f.append([e(w,i) for w in (u,v) for i in bits(t)])
        return f
    assert 5<=d<=9 and 5<=q<=9 and (d!=9 or q==9)
    A=list(range(1,d+1));H=list(range(d+1,N))
    for i in range(1,N):f.append([e(0,i) if i in A else -e(0,i)])
    for i,j in itertools.combinations(A,2):f.append([-e(i,j)])
    for i,j,k in itertools.combinations(range(N),3):f.append([-e(i,j),-e(i,k),-e(j,k)])
    # Saturation: for each nonedge, choose a common neighbor. Implications suffice.
    for i,j in pairs:
        cs=[]
        for k in range(N):
            if k in (i,j):continue
            z=pool.id(('common',i,j,k));cs.append(z)
            f.append([-z,e(i,k)]);f.append([-z,e(j,k)])
        f.append([e(i,j)]+cs)
    for i in range(N):
        xs=[e(i,j) for j in range(N) if i!=j]
        low=9 if d==9 else q if i in A else 5;high=9
        if i==0:low=high=d
        if i==1:low=high=q
        al(xs,low);am(xs,high)
    for i in H:
        al([e(i,j) for j in H if j!=i],11-d)
        f.append([e(i,j) for j in A])
    hs=[e(i,j) for i,j in itertools.combinations(H,2)]
    al(hs,{5:129,6:118,7:104,8:95,9:86}[d],EncType.cardnetwrk)
    am(hs,180-9*d,EncType.cardnetwrk)
    al(list(edge.values()),159,EncType.cardnetwrk)
    return f
def graph(model):
    truth={x for x in model if x>0};a=[0]*N
    for (i,j),x in edge.items():
        if x in truth:a[i]|=1<<j;a[j]|=1<<i
    return a
def cut(s):
    assert len(s)==10 and len(set(s))==10 and min(s)>=0 and max(s)<N
    return [e(i,j) for i,j in itertools.combinations(sorted(s),2)]
def save(p,obj):
    tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(obj,indent=2)+'\n');tmp.replace(p)
def digest(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def replay(d,q,core,out,seconds):
    # Rebuild independently from base and recorded genuine 10-set clauses.
    f=base(d,q,core);seen=set()
    for line in (out/'cuts.jsonl').read_text().splitlines():
        s=tuple(json.loads(line));assert s not in seen;seen.add(s);f.append(cut(s))
    cnf=out/'leaf.cnf';f.to_file(str(cnf));proof=out/'leaf.drat'
    result={'cnf_sha256':digest(cnf),'certificate':'NOT_VERIFIED'}
    def limit():resource.setrlimit(resource.RLIMIT_FSIZE,(512*1024*1024,512*1024*1024))
    try:
        with open(out/'kissat.log','w') as fo:
            r=subprocess.run(['kissat',str(cnf),str(proof)],stdout=fo,stderr=subprocess.STDOUT,timeout=seconds,preexec_fn=limit)
        result['kissat_exit']=r.returncode
        if r.returncode==20:
            with open(out/'drat-trim.log','w') as fo:
                z=subprocess.run(['drat-trim',str(cnf),str(proof)],stdout=fo,stderr=subprocess.STDOUT,timeout=seconds)
            if z.returncode==0 and 's VERIFIED' in (out/'drat-trim.log').read_text(errors='replace'):
                result.update(certificate='VERIFIED_UNSAT',proof_sha256=digest(proof))
                with open(proof,'rb') as fi,gzip.open(out/'leaf.drat.gz','wb',compresslevel=1) as fo:shutil.copyfileobj(fi,fo)
    except (subprocess.TimeoutExpired,OSError) as ex:result['replay_error']=str(ex)
    finally:
        if proof.exists():proof.unlink()
    return result
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--d',type=int,default=0);ap.add_argument('--q',type=int,default=0);ap.add_argument('--core',action='store_true')
    ap.add_argument('--seconds',type=int,default=1200);ap.add_argument('--replay-seconds',type=int,default=300);ap.add_argument('--out',required=True);a=ap.parse_args()
    out=Path(a.out);out.mkdir(parents=True,exist_ok=True);f=base(a.d,a.q,a.core)
    result={'branch':('CORE-C35' if a.core else f'D{a.d}-N{a.q}'),'status':'OPEN','base_vars':f.nv,'base_clauses':len(f.clauses),'models':0,'cuts':0}
    save(out/'result.json',result)
    start=time.monotonic();rng=random.Random(1000*a.d+a.q+12345);seen=set();order=list(range(N))
    with Solver(name='cadical195',bootstrap_with=f.clauses) as sol,open(out/'cuts.jsonl','w',buffering=1) as fo:
        while time.monotonic()-start<a.seconds:
            sol.conf_budget(100000);status=sol.solve_limited()
            if status is None:continue
            if status is False:result['status']='UNSAT_PENDING_REPLAY';break
            g=graph(sol.get_model());result['models']+=1;rng.shuffle(order)
            ss=list(independent(g,10,256,order))
            if not ss:
                assert all(not(g[i]&g[j]) for i,j in pairs if g[i]>>j&1)
                (out/'witness.txt').write_text(''.join(''.join(str(g[i]>>j&1) for j in range(N))+'\n' for i in range(N)))
                result['status']='WITNESS_PENDING_INDEPENDENT_REPLAY';break
            for s in ss:
                assert s not in seen;seen.add(s);sol.add_clause(cut(s));fo.write(json.dumps(s)+'\n')
            result['cuts']=len(seen)
            if result['models']%25==0:save(out/'result.json',result);print(json.dumps(result),flush=True)
    if result['status']=='UNSAT_PENDING_REPLAY':
        result.update(replay(a.d,a.q,a.core,out,a.replay_seconds))
        result['status']='CERTIFIED_UNSAT' if result['certificate']=='VERIFIED_UNSAT' else 'OPEN_UNCERTIFIED_UNSAT'
    result['seconds']=time.monotonic()-start;save(out/'result.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__':main()
