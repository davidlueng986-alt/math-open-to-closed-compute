#!/usr/bin/env python3
"""E073: proof-producing full Type-1 OA search. No unverified UNSAT is counted."""
import argparse, collections, gzip, hashlib, itertools, json, os, resource, shutil, subprocess, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
P=list(itertools.combinations(range(5),2))
CAP=32*1024*1024
SHARD_ARCHIVE_CAP=24*1024*1024

def cases():
    out=[]
    for line in (HERE/"cases.txt").read_text().splitlines():
        cid, flat, *orient=line.split()
        M=[list(map(int,flat[6*r:6*r+6])) for r in range(6)]
        assert all(set(row)==set(range(6)) for row in M)
        assert all({M[r][c] for r in range(6)}==set(range(6)) for c in range(6))
        for i,o in enumerate(orient):
            assert sorted(o)==list("012345")
            out.append((f"{cid}-{i}",M,{int(v):(j//2,j%2) for j,v in enumerate(o)}))
    assert len(out)==124 and len({t[0] for t in out})==124
    return out

def block():
    b={}
    for i,t in enumerate([(0,0,0),(0,1,1),(1,0,1),(1,1,0)]): b[i,i]=t
    for r,c,*t in [(0,1,1,2,2),(1,0,1,3,3),(2,3,0,4,4),(3,2,0,5,5),
                    (0,2,2,1,6),(2,0,3,1,7),(1,3,4,0,8),(3,1,5,0,9),
                    (0,3,6,6,1),(3,0,7,7,1),(1,2,8,8,0),(2,1,9,9,0)]:
        b[r,c]=tuple(t)
    assert len(b)==16
    return b

def points(n,M=None,sm=None,control=None):
    fixed=block() if M is not None else {}
    used=set()
    for (r,c),t in fixed.items():
        for i,j in P:
            q=(r,c)+t
            assert (i,j,q[i],q[j]) not in used
            used.add((i,j,q[i],q[j]))
    out=[]
    for r,c in itertools.product(range(n),repeat=2):
        if (r,c) in fixed:
            out.append((r,c)+fixed[r,c]); continue
        ds=[]
        for k in range(3):
            d=set(range(n))
            if control and r==0: d={c}
            if control and k==0 and c==0: d={r}
            if M is not None:
                if r<4 or c<4: d=set(range(2,10))
                else:
                    mk,bit=sm[M[r-4][c-4]]
                    d={bit} if k==mk else set(range(2,10))
            ds.append(sorted(v for v in d if (0,k+2,r,v) not in used and (1,k+2,c,v) not in used))
        for t in itertools.product(*ds):
            q=(r,c)+t
            if all((i,j,q[i],q[j]) not in used for i,j in P): out.append(q)
    return out

def prune(n,pts):
    """Sound exact-cover propagation: forced resource, incompatible alternatives, zero support."""
    keys=[(i,j,a,b) for i,j in P for a in range(n) for b in range(n)]
    incidence={k:set() for k in keys}
    res=[]
    for idx,p in enumerate(pts):
        rr=tuple((i,j,p[i],p[j]) for i,j in P)
        res.append(rr)
        for k in rr: incidence[k].add(idx)
    live=set(range(len(pts))); forced=set()
    while True:
        if any(not v for v in incidence.values()): return None, len(forced)
        todo={next(iter(v)) for v in incidence.values() if len(v)==1}-forced
        if not todo: break
        for i in sorted(todo):
            if i not in live: return None,len(forced)
            forced.add(i)
            dead=set().union(*(incidence[k] for k in res[i]))-{i}
            if dead&forced: return None,len(forced)
            for j in dead:
                live.remove(j)
                for k in res[j]: incidence[k].remove(j)
    return [pts[i] for i in sorted(live)],len(forced)

class CNF:
    def __init__(self): self.n=0;self.cl=[]
    def var(self): self.n+=1;return self.n
    def add(self,*l): self.cl.append(list(l))
    def ex1(self,l):
        l=list(l);self.cl.append(l)
        if len(l)<=7:
            for a,b in itertools.combinations(l,2): self.add(-a,-b)
        else:
            s=[self.var() for _ in range(len(l)-1)]
            self.add(-l[0],s[0])
            for i in range(1,len(l)-1):
                self.add(-l[i],s[i]);self.add(-s[i-1],s[i]);self.add(-l[i],-s[i-1])
            self.add(-l[-1],-s[-1])
    def write(self,path):
        with open(path,"w") as f:
            f.write(f"p cnf {self.n} {len(self.cl)}\n")
            for c in self.cl: f.write(" ".join(map(str,c))+" 0\n")

def encode(n,pts,variant):
    # Candidate-point exact cover and a factored projection encoding.
    # Both are derived directly from the same allowed tuple set.
    f=CNF(); witness={}
    if variant=="point":
        groups=collections.defaultdict(list)
        for p in pts:
            z=f.var();witness[z]=p
            for i,j in P: groups[i,j,p[i],p[j]].append(z)
        for i,j in P:
            for a,b in itertools.product(range(n),repeat=2): f.ex1(groups[i,j,a,b])
        return f,witness
    # Factored version: x is a cell value, z is a pair at a cell.
    # Explicit triangle support guarantees the local triple lies in pts.
    cells=collections.defaultdict(list)
    for p in pts: cells[p[:2]].append(p[2:])
    x={};z={};glob=collections.defaultdict(list)
    for r,c in itertools.product(range(n),repeat=2):
        tt=cells[r,c];tset=set(tt)
        dom=[sorted({t[k] for t in tt}) for k in range(3)]
        for k in range(3):
            for a in dom[k]: x[r,c,k,a]=f.var()
            f.ex1(x[r,c,k,a] for a in dom[k])
        for i,j in itertools.combinations(range(3),2):
            pp=sorted({(t[i],t[j]) for t in tt})
            if not pp: f.add()
            local=[]
            for a,b in pp:
                q=f.var();z[r,c,i,j,a,b]=q;local.append(q)
                glob[i,j,a,b].append(q)
                f.add(-q,x[r,c,i,a]);f.add(-q,x[r,c,j,b])
            f.ex1(local)
            for a in dom[i]: f.add(-x[r,c,i,a],*(z[r,c,i,j,u,v] for u,v in pp if u==a))
            for b in dom[j]: f.add(-x[r,c,j,b],*(z[r,c,i,j,u,v] for u,v in pp if v==b))
        for t in itertools.product(*dom):
            if t not in tset: f.add(*(-x[r,c,k,t[k]] for k in range(3)))
    for k in range(3):
        for i,a in itertools.product(range(n),repeat=2):
            f.ex1(x[i,c,k,a] for c in range(n) if (i,c,k,a) in x)
            f.ex1(x[r,i,k,a] for r in range(n) if (r,i,k,a) in x)
    for i,j in itertools.combinations(range(3),2):
        for a,b in itertools.product(range(n),repeat=2): f.ex1(glob[i,j,a,b])
    return f,x

def verify(n,ps,allowed):
    if len(ps)!=n*n or len(set(ps))!=n*n or not set(ps)<=allowed: return False
    return all({(p[i],p[j]) for p in ps}==set(itertools.product(range(n),repeat=2)) for i,j in P)

def model_points(n,model,wit,variant):
    if variant=="point": return sorted(p for z,p in wit.items() if z in model)
    cell={}
    for (r,c,k,a),z in wit.items():
        if z in model: cell.setdefault((r,c),{})[k]=a
    return [(r,c,*[t[k] for k in range(3)]) for (r,c),t in sorted(cell.items())]

def limited():
    resource.setrlimit(resource.RLIMIT_FSIZE,(CAP,CAP))

def run_one(n,raw,label,variant,out,budget,keep):
    start=time.monotonic();out.mkdir(exist_ok=True,parents=True)
    p=out/"instance.cnf";proof=out/"proof.drat";log=out/"solver.log";check=out/"checker.log"
    # Preserve proof semantics by encoding original tuple set (not a reduced formula)
    # unless propagation does not remove candidates. Propagation is reported separately.
    reduced,nforced=prune(n,raw)
    f,wit=encode(n,raw,variant);f.write(p)
    info={"case":label,"encoding":variant,"candidates":len(raw),"propagated_candidates":None if reduced is None else len(reduced),"forced":nforced,"variables":f.n,"clauses":len(f.cl),"cnf_sha256":hashlib.sha256(p.read_bytes()).hexdigest()}
    try:
        with log.open("w") as lf:
            proc=subprocess.run(["cadical",str(p),str(proof)],stdout=lf,stderr=subprocess.STDOUT,timeout=budget,preexec_fn=limited)
        rc=proc.returncode
    except subprocess.TimeoutExpired: rc=124
    info["solver_exit"]=rc
    if rc==10:
        true={int(v) for l in log.read_text().splitlines() if l.startswith("v ") for v in l[2:].split() if int(v)>0}
        ps=model_points(n,true,wit,variant)
        assert verify(n,ps,set(raw)),f"invalid witness {label}"
        info["status"]="SAT_VERIFIED";info["points"]=ps
    elif rc==20 and proof.is_file():
        try:
            with check.open("w") as lf:
                v=subprocess.run(["drat-trim",str(p),str(proof),"-t","40"],stdout=lf,stderr=subprocess.STDOUT,timeout=50,preexec_fn=limited)
            ok=v.returncode==0 and "s VERIFIED" in check.read_text(errors="replace")
        except subprocess.TimeoutExpired: ok=False
        info["status"]="UNSAT_CHECKED" if ok else "UNSAT_UNCHECKED"
        if ok:
            info["proof_sha256"]=hashlib.sha256(proof.read_bytes()).hexdigest()
            if keep:
                for source in (p,proof):
                    with source.open("rb") as fi,gzip.open(str(source)+".gz","wb",compresslevel=3) as fo: shutil.copyfileobj(fi,fo)
                info["proof_retained"]=True
    else: info["status"]="UNKNOWN_BUDGET_OR_RESOURCE"
    if "proof_retained" not in info: info["proof_retained"]=False
    for x in (p,proof):
        if x.exists(): x.unlink()
    info["seconds"]=round(time.monotonic()-start,3)
    return info

def main():
    ap=argparse.ArgumentParser();ap.add_argument("shard",type=int);ap.add_argument("shards",type=int);ap.add_argument("out",type=Path);ap.add_argument("--budget",type=int,default=75);a=ap.parse_args()
    a.out.mkdir(parents=True,exist_ok=True)
    cc=cases();variant="point" if a.shard%2==0 else "factored"
    # Both controls use generic normalized complete-square encodings.
    pos=run_one(5,points(5,control=True),"GF5",variant,a.out/"control5",25,False)
    neg=run_one(3,points(3,control=True),"N3",variant,a.out/"control3",25,False)
    assert pos["status"]=="SAT_VERIFIED" and neg["status"]=="UNSAT_CHECKED",(pos,neg)
    rows=[]
    def save():
        output={"problem":"MOLS10-3","shard":a.shard,"shards":a.shards,"scope":"E072 canonical B00 and 124 archived oriented M cases; restricted Type 1 only","controls":[pos,neg],"cases":rows,"global_status":"SAT_VERIFIED" if any(r["status"]=="SAT_VERIFIED" for r in rows) else "OPEN"}
        (a.out/"result.json").write_text(json.dumps(output,indent=2)+"\n")
    for index,(label,M,sm) in enumerate(cc):
        if index%a.shards!=a.shard: continue
        raw=points(10,M,sm);folder=a.out/f"case-{label}"
        info=run_one(10,raw,label,variant,folder,a.budget,True)
        total=sum(p.stat().st_size for p in a.out.rglob("*.gz"))
        if total>SHARD_ARCHIVE_CAP:
            for p in folder.glob("*.gz"): p.unlink()
            info["proof_retained"]=False
        rows.append(info);print(json.dumps(info),flush=True);save()
    save()
if __name__=="__main__": main()
