#!/usr/bin/env python3
"""Whole-cycle decision diagrams; only power-free expanded graphs can be accepted.
Exact finite-domain improvement over the previous one-witness-at-a-time cuts."""
import argparse,itertools,json,pathlib,subprocess,sys,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/"erdos64-threeport-frontier"))
import search as old
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Glucose4
import networkx as nx

def minkowski(a,b):
    z=0
    for i in old.lengths(b): z|=a<<i
    return z

def diagram(cyc,states,limit=40000):
    """Forward all possible sum masks, then remove impossible suffixes.
    A state is a mask of ALL lengths, not a single chosen length."""
    layers=[{1<<len(cyc)}]
    options=[[s["spectra"][p] for s in states] for v,p in cyc]
    total=1
    for row in options:
        nxt={minkowski(a,b) for a in layers[-1] for b in set(row)}
        total+=len(nxt)
        if total>limit:return None
        layers.append(nxt)
    bad=sum(1<<p for p in old.pw(max(m.bit_length()-1 for m in layers[-1])))
    viable=[None]*len(layers)
    viable[-1]={m for m in layers[-1] if m&bad==0}
    for j in reversed(range(len(cyc))):
        viable[j]={m for m in layers[j] if any(minkowski(m,b) in viable[j+1] for b in set(options[j]))}
    return viable,options,total

def encode(cyc,states,pool,var,cnf,limit=40000):
    d=diagram(cyc,states,limit)
    if d is None:return None
    viable,opts,total=d
    root=1<<len(cyc)
    if root not in viable[0]:cnf.append([]);return total
    nodes=[{m:pool.id() for m in sorted(layer)} for layer in viable[:-1]]
    cnf.append([nodes[0][root]])
    for j,(v,p) in enumerate(cyc):
        for m,a in nodes[j].items():
            for k,b in enumerate(opts[j]):
                t=minkowski(m,b)
                if t not in viable[j+1]:cnf.append([-a,-var(v,k)])
                elif j+1<len(cyc):cnf.append([-a,-var(v,k),nodes[j+1][t]])
    return total

def verify_word(cyc,states,word):
    # Different implementation: explicit integer sets, no bit operations.
    sums={len(cyc)}
    for (_,p),k in zip(cyc,word):
        sums={a+b for a in sums for b in old.lengths(states[k]["spectra"][p])}
    return all((x<4 or x&(x-1)) for x in sums)

def controls(states):
    # Compare the full diagram language with direct sumsets on all short words
    # from the real catalogue. No solver result is used as a semantic oracle.
    for r in (3,4):
        cyc=[(j,j%3) for j in range(r)];v,opts,total=diagram(cyc,states)
        for word in itertools.product(range(len(states)),repeat=r):
            m=1<<r;ok=m in v[0]
            for j,k in enumerate(word):
                m=minkowski(m,opts[j][k]);ok=ok and m in v[j+1]
            assert ok==verify_word(cyc,states,word)
    print("DIRECT_DIAGRAM_LANGUAGE_PASS",flush=True)

def make_base(n,m,pool):
    cnf=CNF();var=lambda v,k:v*m+k+1
    for v in range(n):cnf.extend(CardEnc.equals([var(v,k) for k in range(m)],bound=1,vpool=pool,encoding=EncType.seqcounter).clauses)
    return cnf,var

def solve(G,states,seconds,out):
    out.mkdir(parents=True,exist_ok=True);deadline=time.monotonic()+seconds
    n,m=len(G),len(states);pool=IDPool(start_from=n*m+1)
    cnf,var=make_base(n,m,pool)
    try:cycles=sorted(old.getcycles(G,deadline),key=lambda c:(len(c),c))
    except TimeoutError:return dict(status="cycle-enumeration-timeout")
    trace=[]; encoded=set();fallback=0;mx=0
    with Glucose4(bootstrap_with=cnf.clauses) as sol:
        while time.monotonic()<deadline:
            ans=old.timed(sol,deadline-time.monotonic())
            if ans is None:break
            if not ans:
                cnf.to_file(str(out/"problem.cnf"))
                (out/"trace.json").write_text(json.dumps(trace))
                # Rebuild from the exact graph cycles and independently validated
                # spectra; verify deterministic CNF before the proof replay.
                p2=IDPool(start_from=n*m+1);c2,v2=make_base(n,m,p2)
                for kind,idx,data in trace:
                    c=cycles[idx]
                    if kind=="diagram":assert encode(c,states,p2,v2,c2)==data
                    else:
                        assert len(data)==len(c)
                        assert not verify_word(c,states,data)
                        c2.append([-v2(v,k) for (v,p),k in zip(c,data)])
                assert c2.clauses==cnf.clauses
                try:
                    q=subprocess.run(["kissat",str(out/"problem.cnf"),str(out/"proof.drat")],capture_output=True,timeout=90)
                    (out/"kissat.log").write_bytes(q.stdout+q.stderr)
                    if q.returncode==20:
                        q=subprocess.run(["drat-trim",str(out/"problem.cnf"),str(out/"proof.drat")],capture_output=True,timeout=90)
                        (out/"drat.log").write_bytes(q.stdout+q.stderr)
                        if q.returncode==0 and b"s VERIFIED" in q.stdout:
                            return dict(status="UNSAT-DRAT",diagrams=len(encoded),fallback=fallback,largest_diagram=mx,clauses=len(cnf.clauses))
                except subprocess.TimeoutExpired:pass
                return dict(status="UNSAT-no-proof",diagrams=len(encoded),fallback=fallback)
            pos={i for i in sol.get_model() if 0<i<=n*m}
            choice=[next(k for k in range(m) if var(v,k) in pos) for v in range(n)]
            bad=None
            for idx,c in enumerate(cycles):
                word=[choice[v] for v,p in c]
                if old.bad_cycle(c,states,choice) is not None:
                    bad=(idx,c,word);break
            if bad is None:
                H=old.expand(G,states,choice)
                (out/"candidate.g6").write_bytes(nx.to_graph6_bytes(H,header=False))
                (out/"choice.json").write_text(json.dumps(choice))
                try:ok=old.explicit_check(H,time.monotonic()+600)
                except TimeoutError:return dict(status="candidate-verification-timeout",order=len(H))
                assert ok
                return dict(status="ORIGINAL_COUNTEREXAMPLE",order=len(H))
            idx,c,word=bad
            assert idx not in encoded
            before=len(cnf.clauses)
            z=encode(c,states,pool,var,cnf)
            if z is None:
                cnf.append([-var(v,k) for (v,p),k in zip(c,word)])
                trace.append(["word",idx,word]);fallback+=1
            else:
                encoded.add(idx);trace.append(["diagram",idx,z]);mx=max(mx,z)
            sol.append_formula(cnf.clauses[before:])
    return dict(status="TIMEOUT",diagrams=len(encoded),fallback=fallback,largest_diagram=mx)
def main():
    a=argparse.ArgumentParser();a.add_argument("--gadgets",required=True);a.add_argument("--bases",required=True);a.add_argument("--shard",type=int,required=True);a.add_argument("--shards",type=int,required=True);a.add_argument("--seconds",type=int,default=120);a.add_argument("--out",default="out");a=a.parse_args()
    out=pathlib.Path(a.out);out.mkdir(parents=True,exist_ok=True)
    states=old.getstates([json.loads(s) for s in pathlib.Path(a.gadgets).read_text().splitlines() if s.strip()])
    controls(states)
    (out/"states.json").write_text(json.dumps(states))
    print("states",len(states),flush=True)
    for i,line in enumerate(pathlib.Path(a.bases).read_text().splitlines()):
        if i%a.shards!=a.shard:continue
        G=nx.from_graph6_bytes(line.encode());assert all(d==3 for _,d in G.degree)
        t=time.monotonic()
        r=solve(G,states,a.seconds,out/f"base-{i:05d}")
        r.update(index=i,g6=line,n=len(G),seconds=round(time.monotonic()-t,3))
        print(json.dumps(r),flush=True)
        with (out/"results.jsonl").open("a") as f:f.write(json.dumps(r)+"\n")
        if r["status"]=="ORIGINAL_COUNTEREXAMPLE":break
if __name__=="__main__":main()
