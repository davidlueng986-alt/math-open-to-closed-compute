#!/usr/bin/env python3
"""Original Erdős #64 witness search via a minimum-order one-defect graph.
The no-defect branch of the lexicographically minimal near-counterexample is cubic.
Here search the other branch at n=21..28, with necessary minimality constraints.
Any verified SAT graph gives an original counterexample by gluing two copies at
its unique degree-two vertex. UNSAT is a solver report, not an independent proof.
"""
import ast,itertools,json,os,shutil,subprocess,sys,time
from pathlib import Path
import networkx as nx
from pysms.graph_builder import GraphEncodingBuilder

def powers(n):return [2**k for k in range(2,n.bit_length()) if 2**k<=n]

def encode(n,lengths,out,label):
    b=GraphEncodingBuilder(n,directed=False)
    # Full sequential counters: ge3[v] iff degree>=3, ge4[v] iff degree>=4.
    # No arbitrary vertex labeling restrictions: SMS uses isomorphism representatives.
    ge3=[];ge4=[];cubic=[]
    for v in range(n):
        c=b.counterFunction([b.var_edge(v,u) for u in range(n) if u!=v],
            4,atLeast=2,counterType="sequential")
        ge3.append(c[2]);ge4.append(c[3])
        z=b.id();cubic.append(z)
        b.extend([[-z,c[2]],[-z,-c[3]],[z,-c[2],c[3]]])
    # Exactly one degree-2 vertex.
    b.append([-x for x in ge3])
    for u,v in itertools.combinations(range(n),2):
        e=b.var_edge(u,v)
        b.append([ge3[u],ge3[v]])
        # Minimal edge count: no adjacent high vertices.
        b.append([-e,-ge4[u],-ge4[v]])
        # The unique degree-2 vertex has two cubic neighbors.
        b.append([-e,ge3[u],-ge4[v]])
        b.append([-e,ge3[v],-ge4[u]])
    # Every vertex has a cubic neighbor: otherwise removing it creates
    # at most one defect in a strictly smaller near-counterexample.
    for v in range(n):
        candidates=[]
        for u in range(n):
            if u==v:continue
            e=b.var_edge(u,v);z=b.id();candidates.append(z)
            b.extend([[-z,e],[-z,cubic[u]],[z,-e,-cubic[u]]])
        b.append(candidates)
    if 4 in lengths:
        for a,c,d,e in itertools.combinations(range(n),4):
            for seq in ((a,c,d,e),(a,c,e,d),(a,d,c,e)):
                b.append([-b.var_edge(seq[i],seq[(i+1)%4]) for i in range(4)])
    cnf=out/(label+".cnf")
    with cnf.open("w") as f:b.print_dimacs(f)
    cyc=out/(label+".cycles")
    cyc.write_text("".join(str(k)+" "+" ".join(f"{i} {(i+1)%k}" for i in range(k))+"\n" for k in lengths))
    return cnf,cyc

def has_cycle(G,L):
    if L>len(G):return False
    adj={v:tuple(G[v]) for v in G}
    def dfs(a,v,seen,d):
        if d==L:return a in adj[v]
        return any(dfs(a,u,seen|{u},d+1) for u in adj[v] if u>a and u not in seen)
    return any(dfs(a,b,{a,b},2) for a in G for b in adj[a] if b>a)

def check_structure(G):
    d=dict(G.degree());low=[v for v in G if d[v]<3]
    return (nx.is_connected(G) and len(low)==1 and d[low[0]]==2
        and all(d[u]==3 for u in G[low[0]])
        and all(not(d[u]>=4 and d[v]>=4) for u,v in G.edges)
        and all(any(d[u]==3 for u in G[v]) for v in G))

def decode_model(text,n):
    for line in text.splitlines():
        line=line.strip()
        if not line.startswith("[("):continue
        try:E=ast.literal_eval(line)
        except (ValueError,SyntaxError):continue
        if not isinstance(E,list) or any(not isinstance(e,tuple) or len(e)!=2 or any(type(x)!=int or not 0<=x<n for x in e) or e[0]==e[1] for e in E):continue
        G=nx.Graph();G.add_nodes_from(range(n));G.add_edges_from(E)
        if len(E)==G.number_of_edges() and check_structure(G):return G
    raise RuntimeError("SAT output did not contain valid one-defect graph")

def solve(n,lengths,out,label,budget):
    cnf,cyc=encode(n,lengths,out,label)
    exe=shutil.which("smsg") or str(Path.home()/".local/bin/smsg")
    cmd=[exe,"--vertices",str(n),"--connected","--cutoff","0",
        "--frequency-forbidden-subgraphs","5","--forbidden-subgraph-file",str(cyc.resolve()),
        "--dimacs",str(cnf.resolve())]
    stdout=out/(label+".stdout.log");stderr=out/(label+".stderr.log")
    start=time.monotonic()
    with stdout.open("w") as a,stderr.open("w") as b:
        try:
            p=subprocess.run(cmd,stdout=a,stderr=b,timeout=budget)
            rc=p.returncode;status={10:"SAT",20:"UNSAT_SOLVER_REPORTED"}.get(rc,"UNKNOWN_RETURN_CODE")
        except subprocess.TimeoutExpired:rc=None;status="UNKNOWN_TIMEOUT"
    info={"n":n,"forbidden":lengths,"status":status,"return_code":rc,"seconds":round(time.monotonic()-start,3)}
    if status=="SAT":
        G=decode_model(stdout.read_text(),n)
        for L in lengths:
            if has_cycle(G,L):raise RuntimeError(f"independent verifier found C{L}")
        info["status"]="SAT_INDEPENDENTLY_CHECKED"
        info["edges"]=[list(e) for e in G.edges]
        info["graph6"]=nx.to_graph6_bytes(G,header=False).decode().strip()
        return info,G
    return info,None

def glue(K):
    n=len(K);w=next(v for v in K if K.degree(v)==2);assert check_structure(K)
    assert not any(has_cycle(K,L) for L in powers(n))
    labels={v:i for i,v in enumerate(v for v in K if v!=w)}
    G=nx.Graph();G.add_nodes_from(range(2*n-1))
    def lab(v,j):return 2*n-2 if v==w else labels[v]+j*(n-1)
    for j in (0,1):
        for u,v in K.edges:G.add_edge(lab(u,j),lab(v,j))
    assert len(G)==2*n-1 and nx.is_connected(G) and min(dict(G.degree()).values())>=3
    for S in nx.biconnected_components(G):
        H=G.subgraph(S)
        for L in powers(len(H)):assert not has_cycle(H,L)
    return {"original_counterexample_candidate":True,"order":len(G),
        "min_degree":min(dict(G.degree()).values()),"graph6":nx.to_graph6_bytes(G,header=False).decode().strip(),
        "edges":[list(e) for e in G.edges],"root":w,"formalization":"Lean required"}

def main():
    i,s,out=int(sys.argv[1]),int(sys.argv[2]),Path(sys.argv[3])
    if s!=8 or not 0<=i<s:raise ValueError("expected 8 shards")
    out.mkdir(parents=True,exist_ok=True)
    # Positive control exists: subdividing a Heawood-graph edge once
    # has 15 vertices, exactly one degree2, others degree3, no C4.
    c,_=solve(15,[4],out,"control",180)
    if c["status"]!="SAT_INDEPENDENTLY_CHECKED":raise RuntimeError("positive control failed: "+str(c))
    n=21+i;t,K=solve(n,powers(n),out,"target",3600)
    witness=glue(K) if K is not None else None
    if witness:(out/"witness.json").write_text(json.dumps(witness,indent=2)+"\n")
    result={"problem":"ERDOS-64","shard":i,"shards":s,"control":c,"target":t,"witness":witness}
    (out/"result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"n":n,"status":t["status"],"witness":bool(witness)}),flush=True)
if __name__=="__main__":main()
