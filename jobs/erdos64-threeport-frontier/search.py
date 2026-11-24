#!/usr/bin/env python3
"""Search exact vertex substitutions with arbitrary labelled three-port spectra.

Every simple cycle of the expansion either stays within a gadget or visits a
simple cycle of the base, since each gadget has exactly three external edges.
A SAT model chooses a labelled gadget per vertex. A violated cycle yields a
sound blocking clause for all local choices supporting the same path lengths.
Only independent explicit expanded-graph checking accepts a YES counterexample.
UNSAT must be replayed with Kissat/DRAT-trim to be called certified.
"""
import argparse,itertools,json, pathlib, time, threading, subprocess, sys
import networkx as nx
from pysat.solvers import Glucose4
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType

PAIRS=[(0,1),(0,2),(1,2)]
def pw(n):
    p=4
    while p<=n: yield p; p*=2
def mask(ls):
    return sum(1<<i for i in set(ls))
def lengths(m):
    return [i for i in range(m.bit_length()) if (m>>i)&1]
def verify_gadget(r):
    G=nx.from_graph6_bytes(r["g6"].encode())
    assert len(G)==r["n"] and nx.is_connected(G)
    ports=sorted(v for v,d in G.degree if d==2)
    assert ports==r["ports"] and all(d in (2,3) for _,d in G.degree)
    assert not any(len(c) in set(pw(len(G))) for c in nx.simple_cycles(G))
    assert [mask(len(p)-1 for p in nx.all_simple_paths(G,ports[i],ports[j])) for i,j in PAIRS]==r["spectra"]
def getstates(records):
    # The isolated one-vertex gadget has three ports at the same vertex.
    states=[dict(n=1,g6="@",ports=[0,0,0],spectra=[1,1,1])]
    seen={(1,1,1,1)}
    for r in records:
        verify_gadget(r)
        lookup={p:s for p,s in zip(PAIRS,r["spectra"])}
        for perm in itertools.permutations(range(3)):
            sp=[lookup[tuple(sorted((perm[i],perm[j])))] for i,j in PAIRS]
            key=(r["n"],*sp)
            if key in seen:continue
            seen.add(key)
            states.append(dict(n=r["n"],g6=r["g6"],ports=[r["ports"][i] for i in perm],spectra=sp))
    return states

def getcycles(G,deadline):
    adj={v:sorted(G[v]) for v in G}; result=[]
    for s in sorted(G):
        path=[s]
        def dfs(v,visited):
            if time.monotonic()>deadline:raise TimeoutError
            if len(path)>=3 and s in adj[v] and path[1]<v:
                result.append([(a,PAIRS.index(tuple(sorted((adj[a].index(path[j-1]),adj[a].index(path[(j+1)%len(path)])))))) for j,a in enumerate(path)])
            for w in adj[v]:
                if w>s and w not in visited:
                    path.append(w);dfs(w,visited|{w});path.pop()
        dfs(s,{s})
    return result

def bad_cycle(cyc,states,choice):
    # Dynamic programming over exact Minkowski sum; retain one path-length
    # witness per total, not merely an interval.
    sums={len(cyc):()}
    for v,pair in cyc:
        options=lengths(states[choice[v]]["spectra"][pair])
        sums={a+l:pre+(l,) for a,pre in sums.items() for l in options}
    return next((sums[p] for p in pw(max(sums)) if p in sums),None)

def expand(G,states,choice):
    H=nx.Graph(); port={}; next_id=0
    for v in sorted(G):
        s=states[choice[v]];g=nx.from_graph6_bytes(s["g6"].encode());off=next_id
        H.add_nodes_from(off+i for i in g);H.add_edges_from((off+i,off+j) for i,j in g.edges)
        for u,i in zip(sorted(G[v]),s["ports"]):port[v,u]=off+i
        next_id+=len(g)
    H.add_edges_from((port[v,u],port[u,v]) for v,u in G.edges)
    assert nx.is_connected(H) and all(d==3 for _,d in H.degree)
    return H

def explicit_check(H,deadline):
    adj=[sorted(H[v]) for v in range(len(H))];n=len(H);count=0
    for target in pw(n):
        for s in range(n-target+1):
            def dfs(v,seen,k):
                nonlocal count
                count+=1
                if count%2048==0 and time.monotonic()>deadline:raise TimeoutError
                if k==target:return s in adj[v]
                return any(dfs(w,seen|(1<<w),k+1) for w in adj[v] if w>s and not (seen>>w)&1)
            if dfs(s,1<<s,1):return False
    return True

def timed(solver,seconds):
    if seconds<=0:return None
    timer=threading.Timer(seconds,solver.interrupt);timer.start()
    try:return solver.solve_limited(expect_interrupt=True)
    finally:timer.cancel();timer.join();solver.clear_interrupt()

def search(G,states,seconds,out):
    t=time.monotonic();deadline=t+seconds;out.mkdir(parents=True,exist_ok=True)
    n=len(G);m=len(states);pool=IDPool(start_from=n*m+1);cnf=CNF()
    var=lambda v,k:v*m+k+1
    for v in range(n):
        cnf.extend(CardEnc.equals([var(v,k) for k in range(m)],bound=1,vpool=pool,encoding=EncType.seqcounter).clauses)
    try:cycles=getcycles(G,deadline)
    except TimeoutError:return dict(status="cycle-enumeration-timeout")
    indicators={};cuts=[]
    with Glucose4(bootstrap_with=cnf.clauses) as sol:
        def add(c):
            cnf.append(c);sol.add_clause(c)
        def indicator(v,p,l):
            key=(v,p,l)
            if key not in indicators:
                i=pool.id();allowed=[var(v,k) for k,s in enumerate(states) if s["spectra"][p]&(1<<l)]
                assert allowed
                add([-i,*allowed])
                for a in allowed:add([-a,i])
                indicators[key]=i
            return indicators[key]
        while time.monotonic()<deadline:
            ans=timed(sol,deadline-time.monotonic())
            if ans is None:break
            if ans is False:
                # Independent proof production over the exact saved CNF.
                cnf.to_file(str(out/"problem.cnf"))
                (out/"cuts.json").write_text(json.dumps(cuts))
                try:
                    proof=subprocess.run(["kissat",str(out/"problem.cnf"),str(out/"proof.drat")],capture_output=True,timeout=120)
                    (out/"kissat.log").write_bytes(proof.stdout+proof.stderr)
                    if proof.returncode==20:
                        check=subprocess.run(["drat-trim",str(out/"problem.cnf"),str(out/"proof.drat")],capture_output=True,timeout=120)
                        (out/"check.log").write_bytes(check.stdout+check.stderr)
                        if check.returncode==0 and b"s VERIFIED" in check.stdout:
                            return dict(status="fixed-base-UNSAT-DRAT",cuts=len(cuts),cycles=len(cycles))
                except subprocess.TimeoutExpired:pass
                return dict(status="fixed-base-solver-UNSAT-no-certificate",cuts=len(cuts),cycles=len(cycles))
            pos={i for i in sol.get_model() if 0<i<=n*m}
            choice=[next(k for k in range(m) if var(v,k) in pos) for v in range(n)]
            bad=None
            for cycle in cycles:
                path=bad_cycle(cycle,states,choice)
                if path is not None:bad=(cycle,path);break
            if bad is not None:
                cycle,path=bad
                cuts.append([cycle,list(path)])
                add([-indicator(v,p,l) for (v,p),l in zip(cycle,path)])
                continue
            H=expand(G,states,choice)
            (out/"candidate.g6").write_bytes(nx.to_graph6_bytes(H,header=False))
            (out/"choices.json").write_text(json.dumps(choice))
            try:
                ok=explicit_check(H,time.monotonic()+600)
            except TimeoutError:return dict(status="candidate-check-timeout",order=len(H),cuts=len(cuts))
            assert ok,"independent checker rejected candidate"
            return dict(status="ORIGINAL_COUNTEREXAMPLE",order=len(H),cuts=len(cuts))
    return dict(status="search-timeout",cuts=len(cuts),cycles=len(cycles))

def main():
    a=argparse.ArgumentParser();a.add_argument("--gadgets",required=True);a.add_argument("--bases",required=True);a.add_argument("--shard",type=int,required=True);a.add_argument("--shards",type=int,required=True);a.add_argument("--seconds",type=int,default=180);a.add_argument("--out",default="out");args=a.parse_args()
    out=pathlib.Path(args.out);out.mkdir(parents=True,exist_ok=True)
    records=[json.loads(l) for l in pathlib.Path(args.gadgets).read_text().splitlines() if l.strip()]
    states=getstates(records)
    (out/"states.json").write_text(json.dumps(states))
    print("gadgets",len(records),"labelled spectral types",len(states),flush=True)
    for i,line in enumerate(pathlib.Path(args.bases).read_text().splitlines()):
        if i%args.shards!=args.shard:continue
        G=nx.from_graph6_bytes(line.encode());assert all(d==3 for _,d in G.degree)
        r=search(G,states,args.seconds,out/f"base-{i:04d}")
        r.update(index=i,base=line,order_base=len(G),states=len(states))
        print(json.dumps(r),flush=True)
        with (out/"results.jsonl").open("a") as f:f.write(json.dumps(r)+"\n")
        if r["status"]=="ORIGINAL_COUNTEREXAMPLE":break
if __name__=="__main__":main()
