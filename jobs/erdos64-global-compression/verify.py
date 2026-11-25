#!/usr/bin/env python3
"""Independent exact catalogue verification + constructive all-scale
compression controls. Not an exhaustive verification of the original
conjecture. The graph theorem is in README.md."""
import argparse,itertools,json,random
from pathlib import Path
import networkx as nx

CAT=[{"g6":"Bw","n":3,"ports":[0,1,2],"spectra":[6,6,6]},{"g6":"FCptO","n":7,"ports":[1,2,3],"spectra":[124,124,124]},{"g6":"FCZTO","n":7,"ports":[1,2,3],"spectra":[124,124,120]},{"g6":"N?AA@AODAOP_KGGoGH?","n":15,"ports":[4,6,9],"spectra":[32760,32760,32736]}]
PAIRS=list(itertools.combinations(range(3),2))
SINGLE=dict(g6="@",n=1,ports=[0,0,0],spectra=[1]*3)
REPLACEMENT={3:SINGLE,7:CAT[0],15:CAT[1],1:SINGLE}
def graph(r):return nx.from_graph6_bytes(r["g6"].encode())
def paths(g,u,v):
    if u==v:return {0:[u]}
    return {len(p)-1:p for p in nx.all_simple_paths(g,u,v)}
def pairpaths(r):
    G=graph(r)
    return {p:paths(G,r["ports"][p[0]],r["ports"][p[1]]) for p in PAIRS}
def mask(s):return sum(1<<v for v in s)
def power(x):return x>=4 and x&(x-1)==0
def verify_catalogue():
    for r in CAT:
        G=graph(r)
        assert len(G)==r["n"] and nx.is_connected(G)
        assert sorted(v for v,d in G.degree if d==2)==r["ports"]
        assert all(d in (2,3) for _,d in G.degree)
        assert not any(power(len(c)) for c in nx.simple_cycles(G))
        pp=pairpaths(r)
        assert [mask(pp[p]) for p in PAIRS]==r["spectra"]
        for p in PAIRS:
            for l in pairpaths(REPLACEMENT[r["n"]])[p]:
                assert {2*l+1,2*l+2}<=set(pp[p])
    # Any pair of distinct non-singleton blocks with two parallel
    # external edges has a power cycle. So does a singleton with two
    # edges to a block; no duplicate singleton-singleton edge is possible.
    tests=0
    for A,B in itertools.product(CAT+[SINGLE],repeat=2):
        if A["n"]==B["n"]==1:continue
        for p,q in itertools.product(PAIRS,repeat=2):
            assert any(power(x+y+2) for x in pairpaths(A)[p] for y in pairpaths(B)[q])
            tests+=1
    print("CATALOGUE_AND_PARALLEL_EDGE_PASS",tests,flush=True)

def build(base,rs):
    G=nx.Graph();ports={};loc={};off=0
    for v,r in enumerate(rs):
        H=graph(r);loc[v]=[off+i for i in H];G.add_nodes_from(loc[v])
        G.add_edges_from((off+a,off+b) for a,b in H.edges)
        for i,u in enumerate(sorted(base[v])):ports[v,u]=off+r["ports"][i]
        off+=len(H)
    G.add_edges_from((ports[u,v],ports[v,u]) for u,v in base.edges)
    return G,ports,loc
def cyclelift(base,rs,reps,G,portH,cycle,ls):
    # ls contains a path length in every smaller block.
    s=sum(rs[v]["n"]==1 for v in cycle)
    slack=s
    result=[]
    for i,v in enumerate(cycle):
        u,w=cycle[i-1],cycle[(i+1)%len(cycle)]
        a,b=sorted(base[v]).index(u),sorted(base[v]).index(w)
        rec=rs[v]; internal=graph(rec)
        if rec["n"]==1: l=0
        else:
            extra=1 if slack else 0;slack-=extra
            l=2*ls[i]+1+extra
        ps=paths(internal,rec["ports"][a],rec["ports"][b])
        assert l in ps
        # offset computed independently from the actual port map
        offset=portH[v,u]-rec["ports"][a]
        result.extend(offset+j for j in ps[l])
    assert slack==0 and len(result)==len(set(result))
    assert len(result)==2*(len(cycle)+sum(ls))
    assert all(G.has_edge(v,result[(i+1)%len(result)]) for i,v in enumerate(result))
    return len(result)

def control():
    rng=random.Random(640026)
    checked=0;cases=0;max_order=0
    for n in (4,6,8,10,12):
        for rep in range(8):
            base=nx.random_regular_graph(3,n,seed=rng.randrange(2**32))
            if not nx.is_connected(base):continue
            base=nx.convert_node_labels_to_integers(base,ordering="sorted")
            S=set();vs=list(base);rng.shuffle(vs)
            for v in vs:
                if rng.random()<.65 and not S.intersection(base[v]):S.add(v)
            rs=[SINGLE if v in S else rng.choice(CAT) for v in range(n)]
            reps=[REPLACEMENT[r["n"]] for r in rs]
            G,P,loc=build(base,rs);H,HP,hloc=build(base,reps)
            assert len(H)<len(G) and all(d==3 for _,d in G.degree) and all(d==3 for _,d in H.degree)
            max_order=max(max_order,len(G))
            for cyc in nx.simple_cycles(base):
                if len(cyc)<3:continue
                opts=[]
                for i,v in enumerate(cyc):
                    a=sorted(base[v]).index(cyc[i-1]);b=sorted(base[v]).index(cyc[(i+1)%len(cyc)])
                    opts.append(list(paths(graph(reps[v]),reps[v]["ports"][a],reps[v]["ports"][b])))
                # DP stores a witness for every possible reduced-cycle length.
                sums={len(cyc):()}
                for row in opts:sums={t+l:p+(l,) for t,p in sums.items() for l in row}
                for l,ls in sums.items():
                    if power(l):
                        assert cyclelift(base,rs,reps,G,P,cyc,ls)==2*l
                        checked+=1
            cases+=1
    print(json.dumps({"controls":cases,"lifted_power_cycle_lengths":checked,"max_original_order":max_order}),flush=True)

def local_replacements():
    hits=[]
    for rec in CAT:
        for G in nx.graph_atlas_g():
            if not 3<=len(G)<rec["n"] or not nx.is_connected(G):continue
            if any(power(len(c)) for c in nx.simple_cycles(G)):continue
            for p in itertools.permutations(G,3):
                ds=[G.degree(v)+(v in p) for v in G]
                if sum(d<3 for d in ds)>1 or max(ds)<3:continue
                sp=[mask(paths(G,p[a],p[b])) for a,b in PAIRS]
                if all(x&~y==0 for x,y in zip(sp,rec["spectra"])):
                    hits.append({"old":rec["g6"],"new":nx.to_graph6_bytes(G,header=False).decode().strip(),"ports":p,"spectra":sp,"order":len(G),"defects":sum(d<3 for d in ds)})
    print("LOCAL_REPLACEMENT_HITS",json.dumps(hits),flush=True)
if __name__=="__main__":
    verify_catalogue();control();local_replacements()
