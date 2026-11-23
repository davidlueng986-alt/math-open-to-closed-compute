#!/usr/bin/env python3
"""Direct full-original NO search using a rigorously repairable 3-defect bipartite graph.

Odd n=21,23,25,27. Degrees 2 or 3; exactly three vertices of degree 2.
A bipartite coloring forces all 3 degree-2 ports to be on the same side.
Forbid all power-of-two simple cycle lengths <= n. Add an edge between
two ports (only odd new cycles); glue two copies at the remaining port.
The resulting graph has order 2n-1, min degree >=3, and no power cycle.
Any SAT candidate is parsed and independently verified before reporting.
UNSAT reports without an independent proof certificate are not universal proof.
"""
import ast,itertools,json,os,subprocess,sys,time
from pathlib import Path
import networkx as nx
from pysms.graph_builder import GraphEncodingBuilder

def powers(n):
    return [1<<k for k in range(2,n.bit_length()) if (1<<k)<=n]

def encode(n,lengths,out,label):
    b=GraphEncodingBuilder(n,directed=False)
    b.minDegree(2,countertype="sequential")
    b.maxDegree(3,countertype="sequential")
    m=(3*n-3)//2
    b.numEdgesLow(m,countertype="sequential")
    b.numEdgesUpp(m,countertype="sequential")
    # Existential coloring, invariant under any relabeling of the graph.
    color=[b.id() for _ in range(n)]
    b.append([color[0]]) # color reversal only
    for u,v in itertools.combinations(range(n),2):
        e=b.var_edge(u,v)
        b.append([-e,color[u],color[v]])
        b.append([-e,-color[u],-color[v]])
    # Explicit static C4 clauses supplement the forbidden-subgraph oracle.
    if 4 in lengths:
        for a,b1,c,d in itertools.combinations(range(n),4):
            for seq in ((a,b1,c,d),(a,b1,d,c),(a,c,b1,d)):
                b.append([-b.var_edge(seq[i],seq[(i+1)%4]) for i in range(4)])
    cnf=out/(label+".cnf")
    with cnf.open("w") as f:b.print_dimacs(f)
    cyc=out/(label+".cycles")
    cyc.write_text("".join(str(k)+" "+" ".join(f"{i} {(i+1)%k}" for i in range(k))+"\n" for k in lengths))
    return cnf,cyc

def has_cycle(G,L):
    if L>len(G):return False
    # Independent exact DFS for simple (not induced) cycles.
    adj={v:tuple(G[v]) for v in G}
    def dfs(root,u,seen,depth):
        if depth==L:return root in adj[u]
        return any(dfs(root,v,seen|{v},depth+1) for v in adj[u] if v>root and v not in seen)
    return any(dfs(a,b,{a,b},2) for a in G for b in adj[a] if b>a)

def decode_model(text,n):
    for line in text.splitlines():
        line=line.strip()
        if not line.startswith("[("):continue
        try:e=ast.literal_eval(line)
        except (ValueError,SyntaxError):continue
        if not isinstance(e,list) or any(not isinstance(x,tuple) or len(x)!=2 or any(type(i)!=int or not 0<=i<n for i in x) or x[0]==x[1] for x in e):continue
        G=nx.Graph();G.add_nodes_from(range(n));G.add_edges_from(e)
        if len(e)!=G.number_of_edges():continue
        if nx.is_connected(G) and sorted(dict(G.degree()).values())==[2]*3+[3]*(n-3) and nx.is_bipartite(G):
            return G
    raise RuntimeError("SAT output did not contain a valid graph model")

def solve(n,lengths,out,label,budget):
    cnf,cyc=encode(n,lengths,out,label)
    exe=str(Path.home()/".local/bin/smsg")
    cmd=[exe,"--vertices",str(n),"--connected","--cutoff","0",
        "--frequency-forbidden-subgraphs","5","--forbidden-subgraph-file",str(cyc.resolve()),
        "--dimacs",str(cnf.resolve())]
    stdout=out/(label+".stdout.log");stderr=out/(label+".stderr.log")
    start=time.monotonic()
    with stdout.open("w") as a,stderr.open("w") as b:
        try:
            p=subprocess.run(cmd,stdout=a,stderr=b,timeout=budget)
            rc=p.returncode
            status={10:"SAT",20:"UNSAT_SOLVER_REPORTED"}.get(rc,"UNKNOWN_RETURN_CODE")
        except subprocess.TimeoutExpired:rc=None;status="UNKNOWN_TIMEOUT"
    info={"n":n,"forbidden":lengths,"status":status,"return_code":rc,"seconds":round(time.monotonic()-start,3)}
    if status=="SAT":
        G=decode_model(stdout.read_text(),n)
        for L in lengths:
            if has_cycle(G,L):raise RuntimeError(f"independent verifier rejects model: C{L}")
        info["status"]="SAT_INDEPENDENTLY_CHECKED"
        info["graph6"]=nx.to_graph6_bytes(G,header=False).decode().strip()
        info["edges"]=[list(e) for e in G.edges]
        return info,G
    return info,None

def build_witness(K):
    n=len(K);ports=sorted(v for v in K if K.degree(v)==2);a,b,w=ports
    color=nx.bipartite.color(K)
    assert color[a]==color[b]==color[w] and not K.has_edge(a,b)
    H=K.copy();H.add_edge(a,b)
    assert H.degree(w)==2 and all(d>=3 for v,d in H.degree() if v!=w)
    # Independently verify the repaired block, then the whole glued graph by blocks.
    assert not any(has_cycle(H,L) for L in powers(n))
    G=nx.Graph();G.add_nodes_from(range(2*n-1))
    # Map the one port in both copies to the final vertex, all others to disjoint blocks.
    labels={v:i for i,v in enumerate(v for v in H if v!=w)}
    def lab(v,copy):return 2*n-2 if v==w else labels[v]+copy*(n-1)
    for copy in (0,1):
        for u,v in H.edges:G.add_edge(lab(u,copy),lab(v,copy))
    assert len(G)==2*n-1 and nx.is_connected(G) and min(dict(G.degree()).values())>=3
    blocks=list(nx.biconnected_components(G))
    for S in blocks:
        B=G.subgraph(S)
        for L in powers(len(B)):
            assert not has_cycle(B,L),f"glued witness contains C{L}"
    return {"mathematical_status":"FINITE_COUNTEREXAMPLE_INDEPENDENT_DFS_CHECKED",
      "order":len(G),"min_degree":min(dict(G.degree()).values()),"graph6":nx.to_graph6_bytes(G,header=False).decode().strip(),
      "edges":[list(e) for e in G.edges],"source_ports":ports,"added_edge":[a,b],"identified_port":w,
      "block_orders":sorted(map(len,blocks)),"formalization":"still required"}

def main():
    i,s,out=int(sys.argv[1]),int(sys.argv[2]),Path(sys.argv[3])
    if s!=4 or not 0<=i<s:raise ValueError("expected 4 shards")
    out.mkdir(exist_ok=True,parents=True)
    # Heawood graph minus a vertex is a positive control: n=13, 3 degree-2 ports, no C4.
    control,_=solve(13,[4],out,"control",180)
    if control["status"]!="SAT_INDEPENDENTLY_CHECKED":raise RuntimeError("positive control failed: "+str(control))
    n=[21,23,25,27][i];target,K=solve(n,powers(n),out,"target",3600)
    witness=None
    if K is not None:
        witness=build_witness(K)
        (out/"witness.json").write_text(json.dumps(witness,indent=2)+"\n")
    result={"problem":"ERDOS-64","shard":i,"shards":s,"control":control,"target":target,"witness":witness}
    (out/"result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"n":n,"status":target["status"],"witness":bool(witness)}),flush=True)

if __name__=="__main__":main()
