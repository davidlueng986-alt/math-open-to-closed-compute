#!/usr/bin/env python3
"""Exact lazy cardinality model for marked triangle expansions of cubic graphs.

A fixed base is searched over ALL vertex markings unless interrupted. UNSAT
is a solver result for that fixed base only; it is NOT a global proof.
Every putative counterexample is independently checked on the expanded graph.
"""
import argparse, json, math, random, time, threading, pathlib
import networkx as nx
from pysat.solvers import Glucose4
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType

def powers(n):
    p=4
    while p<=n:
        yield p
        p*=2

def forbidden(r):
    for p in powers(3*r):
        lo=max(0,(p-r+1)//2)
        hi=min(r,p-r)
        if lo<=hi: yield lo,hi

class Deadline(Exception): pass

def cycles(adj,maxlen,deadline,marks=0,max_min=None):
    # Every simple cycle once: start is minimum label, orientation fixed.
    nodes=0
    n=len(adj)
    for start in range(n):
        path=[start]
        def dfs(v,seen,t):
            nonlocal nodes
            nodes+=1
            if nodes%2048==0 and time.monotonic()>deadline: raise Deadline()
            r=len(path)
            if r>=3 and start in adj[v] and path[1]<v:
                yield seen,r,t
            if r>=maxlen or (max_min is not None and r+t>=max_min): return
            for w in adj[v]:
                if w>start and not (seen>>w)&1:
                    path.append(w)
                    yield from dfs(w,seen|(1<<w),t+((marks>>w)&1))
                    path.pop()
        yield from dfs(start,1<<start,(marks>>start)&1)

def add_constraint(solver,pool,mask,r):
    lits=[i+1 for i in range(mask.bit_length()) if (mask>>i)&1]
    assert len(lits)==r
    for lo,hi in forbidden(r):
        if lo==0 and hi==r:
            solver.add_clause([])
        elif lo==0:
            solver.append_formula(CardEnc.atleast(lits,hi+1,vpool=pool,encoding=EncType.seqcounter).clauses)
        elif hi==r:
            solver.append_formula(CardEnc.atmost(lits,lo-1,vpool=pool,encoding=EncType.seqcounter).clauses)
        else:
            s=pool.id()
            for c in CardEnc.atmost(lits,lo-1,vpool=pool,encoding=EncType.seqcounter).clauses:
                solver.add_clause([s]+c)
            for c in CardEnc.atleast(lits,hi+1,vpool=pool,encoding=EncType.seqcounter).clauses:
                solver.add_clause([-s]+c)

def solve_timed(solver,seconds):
    if seconds<=0: return None
    timer=threading.Timer(seconds,solver.interrupt); timer.start()
    try: return solver.solve_limited(expect_interrupt=True)
    finally: timer.cancel(); timer.join(); solver.clear_interrupt()

def expansion(G,marks):
    H=nx.Graph(); ports={}; nxt=0
    for v in sorted(G):
        ns=sorted(G[v])
        if (marks>>v)&1:
            vs=list(range(nxt,nxt+3)); nxt+=3
            H.add_edges_from([(vs[0],vs[1]),(vs[1],vs[2]),(vs[2],vs[0])])
            for u,w in zip(ns,vs): ports[v,u]=w
        else:
            H.add_node(nxt)
            for u in ns: ports[v,u]=nxt
            nxt+=1
    for v,u in G.edges: H.add_edge(ports[v,u],ports[u,v])
    assert len(H)==len(G)+2*marks.bit_count()
    assert all(d==3 for _,d in H.degree())
    return H

def independent_check(H,deadline):
    # Explicit expanded-graph DFS, independent of interval transfer.
    adj=[list(H[v]) for v in range(len(H))]
    count=0
    for target in powers(len(H)):
        for s in range(len(H)):
            def rec(v,seen,k):
                nonlocal count
                count+=1
                if count%4096==0 and time.monotonic()>deadline: raise Deadline()
                if k==target: return s in adj[v]
                return any(rec(w,seen|(1<<w),k+1) for w in adj[v] if w>s and not (seen>>w)&1)
            if rec(s,1<<s,1): return target
    return None

def search(G,seconds):
    n=len(G); adj=[sorted(G[v]) for v in range(n)]
    deadline=time.monotonic()+seconds
    pool=IDPool(start_from=n+1); masks=set(); rounds=0
    # Ensure primary variables exist even if there are no short cycles.
    with Glucose4(bootstrap_with=[[i,-i] for i in range(1,n+1)]) as sol:
        def add(mask,r):
            if mask in masks: return
            masks.add(mask); add_constraint(sol,pool,mask,r)
        try:
            for mask,r,_ in cycles(adj,min(9,n),deadline): add(mask,r)
            # Published lower bound: no cubic counterexample of order <=48.
            # The search is for witnesses only; no global inference from this cutoff.
            minmarks=max(0,(50-n+1)//2)
            if minmarks>n: return dict(status="order-below-published-bound",rounds=0)
            if minmarks:
                sol.append_formula(CardEnc.atleast(list(range(1,n+1)),minmarks,vpool=pool,encoding=EncType.seqcounter).clauses)
            while time.monotonic()<deadline:
                ans=solve_timed(sol,deadline-time.monotonic())
                if ans is None: raise Deadline()
                if not ans: return dict(status="fixed-base-solver-UNSAT",rounds=rounds,cycle_sets=len(masks))
                marks=sum(1<<(i-1) for i in sol.get_model() if 1<=i<=n)
                rounds+=1
                lim=max(powers(n+2*marks.bit_count()))
                bad=None
                for mask,r,t in cycles(adj,min(n,lim),deadline,marks,lim):
                    if any(lo<=t<=hi for lo,hi in forbidden(r)):
                        bad=(mask,r); break
                if bad:
                    assert bad[0] not in masks, "SAT model violated a previously encoded cycle constraint"
                    add(*bad)
                    continue
                H=expansion(G,marks)
                try: err=independent_check(H, time.monotonic()+min(600,seconds))
                except Deadline:
                    return dict(status="candidate-independent-check-timeout", marks=marks,edges=list(H.edges()),rounds=rounds)
                assert err is None, ("interval/graph checker mismatch",err)
                return dict(status="COUNTEREXAMPLE", marks=marks,edges=list(H.edges()),rounds=rounds)
        except Deadline: pass
        return dict(status="TIMEOUT",rounds=rounds,cycle_sets=len(masks))

def main():
    p=argparse.ArgumentParser();p.add_argument("--shard",type=int,default=0);p.add_argument("--count",type=int,default=24);p.add_argument("--seconds",type=int,default=120);p.add_argument("--out",default="out/results.jsonl");a=p.parse_args()
    out=pathlib.Path(a.out);out.parent.mkdir(parents=True,exist_ok=True)
    # Verify exact formula for every r,t in a broad finite control range.
    for r in range(3,200):
        for t in range(r+1):
            assert any(l<=t<=h for l,h in forbidden(r))==any(r+t<=p<=r+2*t for p in powers(3*r))
    rng=random.Random(640025+a.shard)
    for j in range(a.count):
        # Each shard spans orders 20..50; the base is not required to be power-free.
        n=20+2*((a.shard*3+j)%16); seed=rng.randrange(2**32)
        G=nx.random_regular_graph(3,n,seed=seed)
        if not nx.is_connected(G): continue
        # Relabel to guarantee canonical 0..n-1 numbering and integer edge lists.
        G=nx.convert_node_labels_to_integers(G,ordering="sorted")
        t=time.monotonic()
        r=search(G,a.seconds)
        r.update(shard=a.shard,index=j,n=n,seed=seed,elapsed=round(time.monotonic()-t,3),base_edges=list(G.edges()))
        with out.open("a") as f: f.write(json.dumps(r)+"\n")
        print(json.dumps({k:v for k,v in r.items() if k not in ("base_edges","edges")}),flush=True)
        if r["status"]=="COUNTEREXAMPLE": break
if __name__=="__main__": main()
