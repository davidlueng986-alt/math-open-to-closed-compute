#!/usr/bin/env python3
"""Finite, reproducible search for Erdős–Gyárfás counterexamples via cyclic covers.

The cubic bases are enumerated up to isomorphism with nauty geng res/mod.
Chord voltages enumerate all C_m covers up to vertex-fibre gauge equivalence.
A simple base cycle of length L with voltage a lifts to a cycle of length
L*(m/gcd(m,a)); voltage pruning is only a sound necessary condition.
Every surviving cover is tested for ALL power-of-two cycle lengths by the
independent C++ verifier. Timeouts are UNKNOWN, never excluded.
This is a finite-family search, not an all-graphs proof.
"""
import argparse,json,math,shutil,subprocess,time
from pathlib import Path
from collections import defaultdict
import numpy as np
import networkx as nx

EXPECTED={4:1,6:2,8:5,10:19,12:85,14:509,16:4060,18:41301,20:510489}
FAMILIES={n:[m for m in range(2,64//n+1) if 41<=n*m<=63] for n in EXPECTED}

def chords_of(g):
    tr=nx.minimum_spanning_tree(g)
    edge_set={tuple(sorted(e)) for e in g.edges}
    tree_set={tuple(sorted(e)) for e in tr.edges}
    chords=sorted(edge_set-tree_set)
    assert nx.is_connected(g) and len(chords)==len(g.edges)-len(g)+1
    return {e:i for i,e in enumerate(chords)}

def cycle_forms(g,length,chords):
    n=len(g);adj=[tuple(g[v]) for v in range(n)]
    forms=set();q=len(chords)
    def dfs(path,used):
        u=path[-1]
        if len(path)==length:
            if path[0] in adj[u] and path[1]<u:
                a=[0]*q
                for x,y in zip(path,path[1:]+path[:1]):
                    e=(min(x,y),max(x,y))
                    if e in chords:a[chords[e]]+=(1 if x<y else -1)
                v=tuple(a);opp=tuple(-x for x in v)
                forms.add(min(v,opp))
            return
        for v in adj[u]:
            if v>path[0] and v not in used:
                dfs(path+[v],used|{v})
    for root in range(n):
        for v in adj[root]:
            if v>root:dfs([root,v],{root,v})
    return sorted(forms)

def prune(g,m,chords,assignments):
    survivors=np.ones(len(assignments),dtype=bool)
    bad=[a for a in range(m) if (m//math.gcd(m,a)) & ((m//math.gcd(m,a))-1)==0]
    for length in (4,8,16):
        if length>len(g):break
        for form in cycle_forms(g,length,chords):
            if not survivors.any():break
            idx=np.flatnonzero(survivors)
            voltage=(assignments[idx].astype(np.int32)@np.array(form,dtype=np.int32))%m
            survivors[idx[np.isin(voltage,bad)]]=False
    return assignments[survivors]

def verify(g6,g,m,chords,allowed,cutoff=10000000):
    edges=[]
    for u,v in g.edges:
        if u>v:u,v=v,u
        edges.append((u,v,chords.get((u,v),-1)))
    lines=[f'{len(g)} {m} {len(edges)} {len(chords)}']
    lines+=[' '.join(map(str,e)) for e in edges]
    lines+=[str(len(allowed))]
    lines+=[' '.join(map(str,a)) for a in allowed]
    cmd=[str(Path(__file__).with_name('cover_check')),str(cutoff)]
    proc=subprocess.run(cmd,input='\n'.join(lines)+'\n',text=True,capture_output=True,timeout=300)
    if proc.returncode:raise RuntimeError(proc.stderr[-3000:])
    witness=[];unknown=0;tested=-1
    for line in proc.stdout.splitlines():
        if line.startswith('WITNESS'):
            shifts=list(map(int,line.split()[1:]))
            if len(shifts)!=len(chords):raise ValueError('bad shift vector')
            witness.append({'base_graph6':g6,'base_order':len(g),'sheets':m,
                            'chord_edges':[list(e) for e in chords],
                            'shifts':shifts,'lift_order':len(g)*m})
        elif line.startswith('STATS'):
            f=list(map(int,line.split()[1:]));tested=f[0];unknown=f[-1]
    if tested!=len(allowed):raise RuntimeError('verifier did not process all inputs')
    return witness,unknown

def main():
    p=argparse.ArgumentParser()
    p.add_argument('shard',type=int)
    p.add_argument('shards',type=int)
    p.add_argument('outdir',type=Path)
    args=p.parse_args()
    if not 0<=args.shard<args.shards<=256:raise ValueError('bad sharding')
    out=args.outdir;out.mkdir(parents=True,exist_ok=True)
    geng=shutil.which('nauty-geng') or shutil.which('geng')
    if not geng:raise RuntimeError('nauty geng missing: no certified coverage')
    totals={};witness=[];unknown=0;start=time.monotonic()
    tables={}
    for n in EXPECTED:
        fam=FAMILIES[n]
        if not fam:continue
        counts={str(m):{'base_graphs':0,'assignments_total':0,
                        'excluded_by_base_cycles':0,'checked_survivors':0,
                        'unknown_cutoffs':0,'witness_count':0} for m in fam}
        cmd=[geng,'-q','-c','-d3','-D3',str(n),f'{args.shard}/{args.shards}']
        proc=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        for raw in proc.stdout:
            g6=raw.strip().decode('ascii')
            if not g6 or g6.startswith('>>'):continue
            g=nx.from_graph6_bytes(g6.encode())
            if len(g)!=n or not nx.is_connected(g) or any(d!=3 for _,d in g.degree()):
                raise ValueError('invalid connected cubic base from geng')
            chords=chords_of(g);q=len(chords)
            for m in fam:
                s=counts[str(m)];s['base_graphs']+=1
                key=(m,q)
                if key not in tables:
                    tables[key]=np.indices((m,)*q,dtype=np.int16).reshape(q,-1).T.copy()
                table=tables[key]
                s['assignments_total']+=len(table)
                allowed=prune(g,m,chords,table)
                s['excluded_by_base_cycles']+=len(table)-len(allowed)
                if len(allowed):
                    hit,miss=verify(g6,g,m,chords,allowed)
                    s['checked_survivors']+=len(allowed)
                    s['unknown_cutoffs']+=miss
                    s['witness_count']+=len(hit)
                    unknown+=miss;witness+=hit
        err=proc.stderr.read().decode('utf-8','replace')
        if proc.wait()!=0:raise RuntimeError('geng failed: '+err[-3000:])
        totals[str(n)]=counts
        print('shard',args.shard,'base-order',n,'count',counts[str(fam[0])]['base_graphs'],
              'seconds',round(time.monotonic()-start,2),flush=True)
    result={'problem':'ERDOS-64','original_status':'OPEN',
            'scope':'cyclic covers of all connected cubic bases order 4..20, total order 41..63',
            'shard':args.shard,'shards':args.shards,
            'graph_base_count_expected':EXPECTED,'families':FAMILIES,
            'statistics':totals,'unknown_cutoffs':unknown,
            'witnesses':witness[:20],'witness_overflow':max(0,len(witness)-20),
            'seconds':round(time.monotonic()-start,3)}
    (out/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    if witness:(out/'witnesses.json').write_text(json.dumps(witness,indent=2)+'\n')
    print('RESULT',json.dumps({'witnesses':len(witness),'unknown':unknown}))

if __name__=='__main__':main()
