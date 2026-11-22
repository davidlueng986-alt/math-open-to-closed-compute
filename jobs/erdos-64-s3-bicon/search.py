#!/usr/bin/env python3
"""Exhaust all connected biconnected cubic bases order 14..20 and their S3 3-sheet covers.

Gauge-fix spanning-tree edges to identity and enumerate all chord permutations.
Use necessary monodromy 3-cycle constraints, then exact independent C++ cycle DFS.
Failure/timeout/cutoffs are *unknown*, never a proof of exclusion.
"""
import json,os,sys,subprocess,shutil,time
from pathlib import Path
import networkx as nx
import numpy as np

EXPECTED={14:509,16:4060,18:41301,20:510489}
P=Path(__file__).resolve().parent

def chords_of(G):
    T=nx.minimum_spanning_tree(G)
    all_edges={tuple(sorted(e)) for e in G.edges}
    tree={tuple(sorted(e)) for e in T.edges}
    return {e:j for j,e in enumerate(sorted(all_edges-tree))}

def cycle_words(G,L,C):
    n=len(G)
    if L>n:return []
    adj=[tuple(G[v]) for v in range(n)]
    words=[]
    def dfs(path,seen):
        u=path[-1]
        if len(path)==L:
            if path[0] in adj[u] and path[1]<u:
                words.append(tuple((C[(min(a,b),max(a,b))],1 if a<b else -1)
                    for a,b in zip(path,path[1:]+path[:1])
                    if (min(a,b),max(a,b)) in C))
            return
        for v in adj[u]:
            if v>path[0] and v not in seen:dfs(path+[v],seen|{v})
    for u in range(n):
        for v in adj[u]:
            if v>u:dfs([u,v],{u,v})
    return words

def parity_patterns(words,q):
    masks=set()
    for word in words:
        mask=0
        for j,d in word:mask^=1<<j
        masks.add(mask)
    return [e for e in range(1<<q) if all(((e&mask).bit_count()%2)==0 for mask in masks)]

def form(word,parity,q):
    """Affine permutation holonomy; compose from rightmost to leftmost.
    Orientation forward: t -> (-1)^b t+a. Reverse: inverse permutation.
    Because the total holonomy sign is +1, the translation form is linear.
    """
    coeff=[0]*q
    sign=1
    for j,d in reversed(word):
        b=(parity>>j)&1
        coeff[j]+=sign*(1 if d==1 else (-1 if b==0 else 1))
        if b:sign=-sign
    if sign!=1:raise AssertionError("parity not even on forbidden base cycle")
    v=tuple(x%3 for x in coeff)
    w=tuple((-x)%3 for x in v)
    return min(v,w)

def independent_verify(g6,G,C,parity,A,limit=3000000):
    ed=[(min(u,v),max(u,v),C.get((min(u,v),max(u,v)),-1)) for u,v in G.edges]
    lines=[f'{len(G)} 3 {len(ed)} {len(C)}']
    lines+=[' '.join(map(str,e)) for e in ed]
    lines+= [str(parity),str(len(A))]
    lines+=[' '.join(map(str,x)) for x in A]
    result=subprocess.run([str(P/'s3_check'),str(limit)],
          input='\n'.join(lines)+'\n',text=True,capture_output=True,timeout=300)
    if result.returncode:raise RuntimeError('C++ verifier failed: '+result.stderr[-2000:])
    witness=[];checked=-1;unknown=0
    for line in result.stdout.splitlines():
        if line.startswith('WITNESS'):
            a=list(map(int,line.split()[1:]))
            if len(a)!=len(C):raise ValueError("invalid witness length")
            witness.append({'base_graph6':g6,'order':len(G)*3,
                            'base_order':len(G),'parity':parity,
                            'chord_edges':[list(e) for e in C],
                            'shifts':a})
        if line.startswith('STATS'):
            data=list(map(int,line.split()[1:]))
            checked=data[0];unknown=data[-1]
    if checked!=len(A):raise RuntimeError("incomplete C++ candidate screening")
    return witness,unknown

def main(shard,shards,out):
    if not 0<=shard<shards<=256:raise ValueError('bad shard')
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    geng=shutil.which('nauty-geng') or shutil.which('geng')
    if not geng:raise RuntimeError('geng missing')
    t0=time.monotonic();stats={};witnesses=[];unknown=0
    tables={}
    for n in EXPECTED:
        st={'base_graphs':0,'biconnected_bases':0,'excluded_nonbiconnected':0,
            'parity_patterns':0,'voltage_assignments_total':0,
            'excluded_by_monodromy':0,'verified_survivors':0,
            'unknown_cutoffs':0,'witnesses':0}
        proc=subprocess.Popen([geng,'-q','-c','-d3','-D3',str(n),f'{shard}/{shards}'],
                              stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        for raw in proc.stdout:
            g6=raw.strip().decode('ascii')
            if not g6 or g6.startswith('>>'):continue
            G=nx.from_graph6_bytes(g6.encode())
            if len(G)!=n or not nx.is_connected(G) or any(d!=3 for v,d in G.degree):
                raise ValueError('invalid cubic graph from geng')
            st['base_graphs']+=1
            if not nx.is_biconnected(G):
                st['excluded_nonbiconnected']+=1
                continue
            st['biconnected_bases']+=1
            C=chords_of(G);q=len(C);words=[]
            for L in (4,8,16): words.extend(cycle_words(G,L,C))
            patterns=parity_patterns(words,q)
            st['parity_patterns']+=len(patterns)
            if q not in tables:
                tables[q]=np.indices((3,)*q,dtype=np.int8).reshape(q,-1).T.copy()
            A=tables[q]
            for p in patterns:
                st['voltage_assignments_total']+=len(A)
                forms={form(word,p,q) for word in words}
                allowed=np.ones(len(A),dtype=bool)
                for f in forms:
                    idx=np.flatnonzero(allowed)
                    if len(idx)==0:break
                    # All holonomy translations on base 4,8,16-cycles must be nonzero in F3.
                    vals=(A[idx].astype(np.int16)@np.array(f,dtype=np.int16))%3
                    allowed[idx[vals==0]]=False
                survivors=A[allowed]
                st['excluded_by_monodromy']+=len(A)-len(survivors)
                # A fixed blocksize prevents oversized subprocess arguments.
                for j in range(0,len(survivors),512):
                    block=survivors[j:j+512]
                    hit,miss=independent_verify(g6,G,C,p,block)
                    st['verified_survivors']+=len(block)
                    st['unknown_cutoffs']+=miss
                    st['witnesses']+=len(hit)
                    unknown+=miss
                    witnesses.extend(hit)
        err=proc.stderr.read().decode('utf-8','replace')
        if proc.wait()!=0:raise RuntimeError('geng failed: '+err[-2000:])
        stats[str(n)]=st
        print(f'shard={shard} n={n} {st} seconds={time.monotonic()-t0:.2f}',flush=True)
    result={'problem':'ERDOS-64','original_status':'OPEN',
            'scope':'ALL S3 three-sheet covers of connected biconnected cubic bases of orders 14,16,18,20 only',
            'shard':shard,'shards':shards,'expected_all_connected_cubic_bases':EXPECTED,
            'statistics':stats,'witnesses':witnesses[:10],
            'witness_overflow':max(0,len(witnesses)-10),
            'unknown_cutoffs':unknown,'seconds':round(time.monotonic()-t0,3)}
    (out/'result.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    if witnesses:(out/'witnesses.json').write_text(json.dumps(witnesses,indent=2)+'\n')

if __name__=='__main__':
    main(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3])
