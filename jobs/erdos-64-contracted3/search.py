#!/usr/bin/env python3
"""Erdos 64: degree-4 C3 covers made from edge-contractions of cubic bases.
Each voltage that fails the monodromy sieve is soundly ruled out.
Every survivor is checked for simple C4/C8/C16/C32 by independent C++.
An exhaustive result only covers the specified contraction-cover class.
"""
import json, sys, subprocess, shutil, time
from pathlib import Path
import networkx as nx
import numpy as np

COUNTS={16:4060,18:41301}

def chords(G):
    T=nx.minimum_spanning_tree(G)
    base={tuple(sorted(e)) for e in G.edges}
    tree={tuple(sorted(e)) for e in T.edges}
    return {e:i for i,e in enumerate(sorted(base-tree))}

def forms(G,L,C):
    n=len(G);q=len(C);adj=[tuple(G[i]) for i in range(n)];result=set()
    if L>n:return result
    def dfs(path,used):
        x=path[-1]
        if len(path)==L:
            if path[0] in adj[x] and path[1]<x:
                v=[0]*q
                for a,b in zip(path,path[1:]+path[:1]):
                    e=(min(a,b),max(a,b))
                    if e in C:v[C[e]]+=(1 if a<b else -1)
                u=tuple(v);result.add(min(u,tuple(-j for j in u)))
            return
        for w in adj[x]:
            if w>path[0] and w not in used:dfs(path+[w],used|{w})
    for a in range(n):
        for b in adj[a]:
            if b>a:dfs([a,b],{a,b})
    return result

def survive(G,C,table):
    idx=np.arange(len(table),dtype=np.int32)
    for L in (4,8,16):
        for f in forms(G,L,C):
            if not len(idx):return idx
            d=(table[idx].astype(np.int16)@np.array(f,dtype=np.int16))%3
            idx=idx[d!=0]
    return idx

def verify(G,C,V,limit=10000000):
    edges=[(min(a,b),max(a,b),C.get((min(a,b),max(a,b)),-1)) for a,b in G.edges]
    lines=[f'{len(G)} 3 {len(edges)} {len(C)}']
    lines+=[' '.join(map(str,e)) for e in edges]
    lines.append(str(len(V)))
    lines+=[' '.join(map(str,v)) for v in V]
    p=subprocess.run([str(Path(__file__).with_name('cover_check')),str(limit)],
        input='\n'.join(lines)+'\n',text=True,capture_output=True,timeout=360)
    if p.returncode:raise RuntimeError('verifier error: '+p.stderr[-2000:])
    witnesses=[];seen=-1;unknown=0
    for line in p.stdout.splitlines():
        if line.startswith('WITNESS'):
            w=list(map(int,line.split()[1:]))
            if len(w)!=len(C):raise RuntimeError('corrupt witness')
            witnesses.append(w)
        elif line.startswith('STATS'):
            a=list(map(int,line.split()[1:]));seen=a[0];unknown=a[-1]
    if seen!=len(V):raise RuntimeError('missing verifier output')
    return witnesses,unknown

def run(shard,shards,out):
    if not(0<=shard<shards<=256):raise ValueError('bad shard')
    gen=shutil.which('nauty-geng') or shutil.which('geng')
    if not gen:raise RuntimeError('nauty geng missing')
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    counts={};witnesses=[];start=time.monotonic();cache={}
    for n in COUNTS:
        st={'base_graphs':0,'triangle_free_contraction_edges':0,'skipped_triangle_edges':0,
            'voltage_assignments_total':0,'excluded_by_monodromy':0,
            'exact_checked':0,'exact_unknown':0,'witnesses':0}
        cmd=[gen,'-q','-c','-d3','-D3',str(n),f'{shard}/{shards}']
        proc=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        for raw in proc.stdout:
            g6=raw.strip().decode('ascii')
            if not g6 or g6.startswith('>>'):continue
            F=nx.from_graph6_bytes(g6.encode())
            if len(F)!=n or not nx.is_connected(F) or any(d!=3 for _,d in F.degree()):
                raise RuntimeError('invalid cubic generator input')
            st['base_graphs']+=1
            for a,b in F.edges:
                if set(F[a])&set(F[b]):
                    st['skipped_triangle_edges']+=1
                    continue
                st['triangle_free_contraction_edges']+=1
                G=nx.convert_node_labels_to_integers(nx.contracted_edge(F,(a,b),self_loops=False))
                if len(G)!=n-1 or any(d<3 for _,d in G.degree()) or max(dict(G.degree()).values())!=4:
                    raise RuntimeError('bad contraction')
                C=chords(G);q=len(C)
                if q not in cache:
                    cache[q]=np.indices((3,)*q,dtype=np.int8).reshape(q,-1).T.copy()
                table=cache[q]
                st['voltage_assignments_total']+=len(table)
                allowed=survive(G,C,table)
                st['excluded_by_monodromy']+=len(table)-len(allowed)
                if len(allowed):
                    for j in range(0,len(allowed),512):
                        w,unknown=verify(G,C,table[allowed[j:j+512]])
                        st['exact_checked']+=min(512,len(allowed)-j)
                        st['exact_unknown']+=unknown
                        st['witnesses']+=len(w)
                        for shifts in w:
                            witnesses.append({'base_graph6':g6,'contracted_edge':[a,b],
                                'contracted_base_graph6':nx.to_graph6_bytes(G,header=False).decode().strip(),
                                'base_order':len(G),'lift_order':3*len(G),
                                'chord_edges':[list(e) for e in C],
                                'shifts':shifts})
        err=proc.stderr.read().decode('utf-8','replace')
        if proc.wait()!=0:raise RuntimeError('geng failed: '+err[-2000:])
        counts[str(n)]=st
        print(f'shard={shard} F_order={n} {st} seconds={time.monotonic()-start:.1f}',flush=True)
    res={'problem':'ERDOS-64','status':'OPEN',
         'scope':'C3 covers of one-edge contractions of all connected cubic bases order 16 and 18',
         'shard':shard,'shards':shards,'expected_counts':COUNTS,
         'statistics':counts,'witnesses':witnesses[:25],
         'witness_overflow':max(0,len(witnesses)-25),
         'elapsed_seconds':time.monotonic()-start}
    (out/'result.json').write_text(json.dumps(res,sort_keys=True,indent=2)+'\n')
    if witnesses:(out/'witnesses.json').write_text(json.dumps(witnesses,indent=2)+'\n')

if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3])
