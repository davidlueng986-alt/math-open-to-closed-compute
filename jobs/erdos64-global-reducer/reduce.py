#!/usr/bin/env python3
"""Unbounded input-size certified descent engine for Erdos 64.
No finite bound is assumed by the reduction. Failure to find a rule is
IRREDUCIBLE-IN-THIS-SYSTEM, never proof of the conjecture or counterexample.
"""
import argparse,collections,itertools,json,random,sys,time
from pathlib import Path
import networkx as nx
from pysat.solvers import Glucose4
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"erdos64-global-compression"))
import verify as V

LOCAL={
    "FCptO":dict(g6="EZEG",n=6,ports=[0,1,4],spectra=[60,28,60]),
    "N?AA@AODAOP_KGGoGH?":dict(g6="M?AA@AOQDAE_E_OK?",n=14,ports=[5,4,7],spectra=[16368,7384,16352]),
}
def edge(a,b):return (min(a,b),max(a,b))
def isnear(G):
    ds=[d for _,d in G.degree]
    return bool(ds) and max(ds)>=3 and sum(d<3 for d in ds)<=1

def cut_triples(G):
    """A set is a cut iff it has even intersection with every fundamental
    cycle. Enumerate exactly all three-edge cuts by xor of column signatures.
    O(m^2 + output) signature lookup, aside from basis construction."""
    E=sorted(edge(a,b) for a,b in G.edges);idx={e:i for i,e in enumerate(E)}
    T=nx.bfs_tree(G,min(G)).to_undirected()
    assert len(T)==len(G)
    te={edge(a,b) for a,b in T.edges}
    sig=[0]*len(E)
    bit=1
    for i,(a,b) in enumerate(E):
        if (a,b) in te:continue
        sig[i]|=bit
        path=nx.shortest_path(T,a,b)
        for x,y in zip(path,path[1:]):sig[idx[edge(x,y)]]|=bit
        bit<<=1
    buckets=collections.defaultdict(list)
    for i,s in enumerate(sig):buckets[s].append(i)
    for i in range(len(E)):
        for j in range(i+1,len(E)):
            for k in buckets.get(sig[i]^sig[j],()):
                if k>j:yield (E[i],E[j],E[k])

def discover(G):
    found={}
    for cut in cut_triples(G):
        T=G.copy();T.remove_edges_from(cut)
        for S0 in nx.connected_components(T):
            S=frozenset(S0)
            if S in found or len(S) not in (3,7,15):continue
            if any(G.degree(v)!=3 for v in S):continue
            boundary=list(nx.edge_boundary(G,S))
            if len(boundary)!=3 or len({a for a,b in boundary})!=3:continue
            for r in V.CAT:
                if r["n"]!=len(S):continue
                m=nx.algorithms.isomorphism.GraphMatcher(G.subgraph(S),V.graph(r))
                mp=next(m.isomorphisms_iter(),None)
                if mp is None:continue
                inv={v:k for k,v in mp.items()}
                ports=[inv[x] for x in r["ports"]]
                assert set(ports)=={a for a,b in boundary}
                found[S]={"S":S,"rec":r,"ports":ports}
                break
    return list(found.values())

def cover(G,candidates):
    """Exactly disjoint catalogue blocks covering at least one endpoint
    of every edge, i.e. the leftover singleton vertices are independent."""
    if not candidates:return None
    at=collections.defaultdict(list)
    for i,c in enumerate(candidates,1):
        for v in c["S"]:at[v].append(i)
    cnf=[list(range(1,len(candidates)+1))]
    for vs in at.values():
        cnf.extend([-a,-b] for a,b in itertools.combinations(vs,2))
    for a,b in G.edges:
        cnf.append(sorted(set(at[a]+at[b])))
    with Glucose4(bootstrap_with=cnf) as sol:
        if not sol.solve():return None
        selected=[candidates[i-1] for i in sol.get_model() if 1<=i<=len(candidates)]
    covered=set()
    for c in selected:
        assert not covered.intersection(c["S"])
        covered.update(c["S"])
    assert all(a in covered or b in covered for a,b in G.edges)
    return selected

def powercycle(G,seconds=1.0):
    """Explicit witness finder; None is not used as a power-free certificate."""
    end=time.monotonic()+seconds;steps=0
    adj={v:sorted(G[v]) for v in G}
    for P in (2**k for k in range(2,len(G).bit_length()) if 2**k<=len(G)):
        for s in sorted(G):
            path=[s]
            def dfs(v,seen):
                nonlocal steps
                steps+=1
                if steps%1024==0 and time.monotonic()>end:raise TimeoutError
                if len(path)==P:return list(path) if s in adj[v] else None
                for w in adj[v]:
                    if w>s and w not in seen:
                        path.append(w);z=dfs(w,seen|{w});path.pop()
                        if z is not None:return z
                return None
            try:r=dfs(s,{s})
            except TimeoutError:return None
            if r is not None:return r
    return None

def checkcycle(G,C):
    assert V.power(len(C)) and len(C)==len(set(C))
    assert all(G.has_edge(a,C[(i+1)%len(C)]) for i,a in enumerate(C))

def exact_paths(G,S,a,b):
    if a==b:return {0:[a]}
    return V.paths(G.subgraph(S),a,b)

def make_step(G,selected,scale):
    """Return a direct witness on parallel quotient edges, or a reduction
    object with actual edge/port correspondence for lifting."""
    covered=set();blocks=[]
    for c in selected:
        assert not covered.intersection(c["S"]);covered.update(c["S"])
        rec=c["rec"]
        rep=V.REPLACEMENT[rec["n"]] if scale==2 else LOCAL[rec["g6"]]
        blocks.append(dict(S=c["S"],oldports=c["ports"],rep=rep,nontriv=True))
    for v in sorted(set(G)-covered):
        blocks.append(dict(S={v},oldports=[v],rep=V.SINGLE,nontriv=False))
    oldblock={v:i for i,b in enumerate(blocks) for v in b["S"]}
    Q=collections.defaultdict(list)
    for a,b in G.edges:
        i,j=oldblock[a],oldblock[b]
        if i==j:continue
        if i>j:i,j,a,b=j,i,b,a
        Q[i,j].append((a,b))
    for (i,j),es in Q.items():
        if len(es)<2:continue
        for (a1,b1),(a2,b2) in itertools.combinations(es,2):
            for x,P in exact_paths(G,blocks[i]["S"],a1,a2).items():
                for y,T in exact_paths(G,blocks[j]["S"],b2,b1).items():
                    if V.power(x+y+2):
                        C=P+T;checkcycle(G,C);return ("WITNESS",C)
        raise AssertionError("catalogue parallel-edge obstruction failed")
    H=nx.Graph();newblock={};portmap={};off=0
    for i,b in enumerate(blocks):
        R=V.graph(b["rep"]);H.add_nodes_from(off+v for v in R)
        H.add_edges_from((off+a,off+c) for a,c in R.edges)
        newblock.update({off+v:i for v in R})
        for a,p in zip(b["oldports"],b["rep"]["ports"]):portmap[a]=off+p
        off+=len(R)
    cross={}
    for es in Q.values():
        a,b=es[0];x,y=portmap[a],portmap[b]
        assert not H.has_edge(x,y)
        H.add_edge(x,y);cross[x,y]=(a,b);cross[y,x]=(b,a)
    assert len(H)<len(G) and isnear(H) and nx.is_connected(H)
    return ("REDUCTION",dict(old=G,new=H,blocks=blocks,newblock=newblock,cross=cross,scale=scale))

def lift(step,C):
    """Exact graph-level reconstruction, not just a length calculation."""
    H,G=step["new"],step["old"];checkcycle(H,C)
    bmap=step["newblock"];blocks=step["blocks"];cross=step["cross"]
    start=next((i for i,v in enumerate(C) if bmap[v]!=bmap[C[i-1]]),None)
    assert start is not None,"no internal power cycles in replacement"
    C=C[start:]+C[:start]
    segments=[(b,list(g)) for b,g in itertools.groupby(C,key=lambda v:bmap[v])]
    assert len(segments)==len({b for b,p in segments})
    slack=sum(not blocks[b]["nontriv"] for b,p in segments) if step["scale"]==2 else 0
    out=[]
    for i,(b,P) in enumerate(segments):
        prev=segments[i-1][1][-1];nxt=segments[(i+1)%len(segments)][1][0]
        a=cross[prev,P[0]][1];z=cross[P[-1],nxt][0]
        l=len(P)-1
        if step["scale"]==2 and blocks[b]["nontriv"]:
            extra=int(slack>0);slack-=extra;l=2*l+1+extra
        paths=exact_paths(G,blocks[b]["S"],a,z);assert l in paths
        out+=paths[l]
    assert slack==0 and len(out)==step["scale"]*len(C)
    checkcycle(G,out);return out

def reduce(G,max_steps=10000,find_cycles=True):
    assert nx.is_connected(G) and isnear(G)
    # Input graph6 labels are consecutive; every new graph has the same property.
    chain=[];initial=G;witness=None;log=[]
    for k in range(max_steps):
        candidates=discover(G);selected=cover(G,candidates);scale=2
        if selected is None and min(dict(G.degree).values())>=3:
            selected=next(([c] for c in candidates if c["rec"]["g6"] in LOCAL),None);scale=1
        if selected is None:break
        typ,result=make_step(G,selected,scale)
        if typ=="WITNESS":witness=result;break
        log.append(dict(before=len(G),after=len(result["new"]),scale=scale,
                        blocks=[sorted(c["S"]) for c in selected],
                        old_g6=nx.to_graph6_bytes(G,header=False).decode().strip(),
                        new_g6=nx.to_graph6_bytes(result["new"],header=False).decode().strip(),
                        catalogue=[c["rec"]["g6"] for c in selected],
                        oldports=[c["ports"] for c in selected]))
        chain.append(result);G=result["new"]
    if witness is None and find_cycles:witness=powercycle(G)
    if witness is not None:
        for step in reversed(chain):witness=lift(step,witness)
        checkcycle(initial,witness)
    return dict(original=len(initial),residual=len(G),steps=len(chain),
                status="POWER-CYCLE-VERIFIED" if witness is not None else "NO-FURTHER-RULE-OR-WITNESS",
                cycle=witness,log=log,residual_g6=nx.to_graph6_bytes(G,header=False).decode().strip())

def controls():
    # Independent brute-force cut-space equality on all connected small
    # atlas graphs with at least 3 vertices (not a sample of the theorem).
    checked=0
    for G in nx.graph_atlas_g():
        if not 3<=len(G)<=6 or not nx.is_connected(G):continue
        brute=set()
        vs=sorted(G)
        for bits in range(1,1<<(len(vs)-1)):
            S={vs[i] for i in range(len(vs)-1) if bits>>i&1}
            e=tuple(sorted(edge(a,b) for a,b in nx.edge_boundary(G,S)))
            if len(e)==3:brute.add(e)
        assert set(cut_triples(G))==brute
        checked+=1
    print("EXACT_CUT_SPACE_CONTROL_PASS",checked,flush=True)
    # These known graph6 rules are rechecked without the C++ generator.
    for old,R in LOCAL.items():
        A=next(x for x in V.CAT if x["g6"]==old);H=V.graph(R)
        assert len(H)<A["n"] and nx.is_connected(H)
        assert not any(V.power(len(c)) for c in nx.simple_cycles(H))
        assert sum(H.degree(v)+(v in R["ports"])<3 for v in H)==1
        assert [V.mask(V.paths(H,R["ports"][i],R["ports"][j])) for i,j in V.PAIRS]==R["spectra"]
        assert all(a&~b==0 for a,b in zip(R["spectra"],A["spectra"]))
    print("LOCAL_RULES_REPLAY_PASS",len(LOCAL),flush=True)

def main():
    a=argparse.ArgumentParser();a.add_argument("--input");a.add_argument("--out",default="out/results.jsonl");a.add_argument("--synthetic",action="store_true");args=a.parse_args()
    controls();out=Path(args.out);out.parent.mkdir(parents=True,exist_ok=True)
    gs=[]
    if args.synthetic:
        rng=random.Random(64)
        for n in (4,6,8,10,12,16,24,32,48,64):
            base=nx.random_regular_graph(3,n,seed=rng.randrange(2**32))
            if not nx.is_connected(base):continue
            base=nx.convert_node_labels_to_integers(base,ordering="sorted")
            S=set()
            for v in sorted(base):
                if not S.intersection(base[v]) and rng.random()<.6:S.add(v)
            rec=[V.SINGLE if v in S else rng.choice(V.CAT) for v in sorted(base)]
            G,_,_=V.build(base,rec);gs.append(G)
    if args.input:
        gs += [nx.from_graph6_bytes(s.encode()) for s in Path(args.input).read_text().splitlines() if s.strip()]
    for i,G in enumerate(gs):
        t=time.monotonic();r=reduce(G,find_cycles=len(G)<=200)
        r.update(index=i,seconds=round(time.monotonic()-t,3))
        print(json.dumps({k:v for k,v in r.items() if k not in ("log","residual_g6","cycle")}),flush=True)
        with out.open("a") as f:f.write(json.dumps(r)+"\n")
if __name__=="__main__":main()
