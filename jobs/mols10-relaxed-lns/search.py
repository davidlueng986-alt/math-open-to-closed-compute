#!/usr/bin/env python3
"""Bounded constructive search; no timeout or neighborhood UNSAT implies global UNSAT."""
import argparse, collections, json, random, time
from pathlib import Path
from ortools.sat.python import cp_model

PAIRS=((0,1),(0,2),(1,2))
def scores(s):
    n=len(s[0]); expected=set(range(n))
    assert len(s)==3
    for a in s:
        assert len(a)==n and all(len(r)==n and set(r)==expected for r in a)
        assert all({a[r][c] for r in range(n)}==expected for c in range(n))
    return [len({(s[i][r][c],s[j][r][c]) for r in range(n) for c in range(n)}) for i,j in PAIRS]

def key(sc):
    return (min(sc),sum(sc),sorted(sc))
def record_key(sc):
    t=sorted(sc)
    return (t[0],sum(t)) if t[1:]==[100,100] else (-1,sum(t))

def solve(s, free, target, seconds, seed, relaxed=False):
    n=len(s[0]); cells=[(r,c) for r in range(n) for c in range(n)]
    fixed=set(cells)-set(free)
    m=cp_model.CpModel(); x={}; val={}; dom={}
    for k in range(3):
        for r,c in cells:
            if (r,c) in fixed:
                d=[s[k][r][c]]
            else:
                d=sorted(set(range(n))-{s[k][rr][cc] for rr,cc in fixed if rr==r or cc==c})
            if not d: return "EMPTY_DOMAIN",None,None
            dom[k,r,c]=d
            for v in d:
                x[k,r,c,v]=m.NewBoolVar(f"x_{k}_{r}_{c}_{v}")
            m.AddExactlyOne([x[k,r,c,v] for v in d])
            for v in d: m.AddHint(x[k,r,c,v],int(v==s[k][r][c]))
        for r in range(n):
            for v in range(n): m.AddExactlyOne([x[k,r,c,v] for c in range(n) if v in dom[k,r,c]])
        for c in range(n):
            for v in range(n): m.AddExactlyOne([x[k,r,c,v] for r in range(n) if v in dom[k,r,c]])
    totals=[]
    for idx,(i,j) in enumerate(PAIRS):
        used={(s[i][r][c],s[j][r][c]) for r,c in fixed}
        if target[idx]==n*n and len(used)!=len(fixed): return "FIXED_COLLISION",None,None
        hits=collections.defaultdict(list)
        for r,c in free:
            for a in dom[i,r,c]:
                for b in dom[j,r,c]:
                    p=(a,b)
                    l1=x[i,r,c,a]; l2=x[j,r,c,b]
                    if target[idx]==n*n and p in used:
                        m.AddBoolOr([l1.Not(),l2.Not()])
                    elif p not in used:
                        z=m.NewBoolVar(f"z_{i}_{j}_{r}_{c}_{a}_{b}")
                        m.AddImplication(z,l1);m.AddImplication(z,l2)
                        m.AddBoolOr([l1.Not(),l2.Not(),z])
                        hits[p].append(z)
        if target[idx]==n*n:
            for a in range(n):
                for b in range(n):
                    if (a,b) not in used: m.AddExactlyOne(hits[a,b])
            totals.append(n*n)
        else:
            present=[]
            for p,lits in hits.items():
                z=m.NewBoolVar(f"present_{i}_{j}_{p[0]}_{p[1]}")
                m.AddMaxEquality(z,lits);present.append(z)
            total=len(used)+sum(present)
            m.Add(total>=target[idx]);totals.append(total)
    if relaxed:
        m.Maximize(totals[0]+totals[1]+2*totals[2])
    else:
        m.Maximize(sum(totals))
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=seconds
    solver.parameters.num_search_workers=4
    solver.parameters.random_seed=seed
    status=solver.Solve(m)
    stat={"status":solver.StatusName(status),"seconds":solver.WallTime(),"branches":solver.NumBranches(),"conflicts":solver.NumConflicts()}
    if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE): return stat,None,None
    out=[[[next(v for v in dom[k,r,c] if solver.BooleanValue(x[k,r,c,v])) for c in range(n)] for r in range(n)] for k in range(3)]
    sc=scores(out)
    assert all(a>=b for a,b in zip(sc,target))
    assert all(out[k][r][c]==s[k][r][c] for r,c in fixed for k in range(3))
    return stat,out,sc

def window(s,rng,number,mode):
    cells=[(r,c) for r in range(10) for c in range(10)]
    mandatory=set()
    # Include all cells involved in repeated pairs across the three projections.
    for i,j in PAIRS:
        count=collections.Counter((s[i][r][c],s[j][r][c]) for r,c in cells)
        mandatory.update((r,c) for r,c in cells if count[s[i][r][c],s[j][r][c]]>1)
    if mode==1:
        rows=rng.sample(range(10),5)
        mandatory.update((r,c) for r in rows for c in range(10))
    if len(mandatory)>number:
        # Prioritize cells implicated in collisions, then diversify using seeded choice.
        mandatory=set(rng.sample(sorted(mandatory),number))
    return sorted(mandatory|set(rng.sample([p for p in cells if p not in mandatory],number-len(mandatory))))

def main():
    ap=argparse.ArgumentParser();ap.add_argument("shard",type=int);ap.add_argument("shards",type=int)
    ap.add_argument("out",type=Path);ap.add_argument("--seconds",type=int,default=240);a=ap.parse_args()
    a.out.mkdir(parents=True,exist_ok=True)
    baseline=json.loads(Path(__file__).with_name("baseline.json").read_text())["squares"]
    assert scores(baseline)==[100,100,91]
    # Positive control: full 3-MOLS(5) with two rows unfrozen, all 3 exact overlays.
    c=[[[ (r+k*j)%5 for j in range(5)] for r in range(5)] for k in (1,2,3)]
    st,w,sc=solve(c,[(r,j) for r in range(2) for j in range(5)],[25]*3,15,1)
    assert w is not None and sc==[25]*3,(st,sc)
    rng=random.Random(20261124+a.shard)
    current=baseline;best=baseline;bestsc=scores(best);events=[]
    def save():
        result={"problem":"MOLS10-3","shard":a.shard,"shards":a.shards,"scope":"bounded 65-70-cell joint Latin-square LNS","mathematical_status":"YES_WITNESS" if bestsc==[100]*3 else "OPEN","best_scores":bestsc,"best_squares":best,"positive_control":"PASS","events":events}
        (a.out/"result.json").write_text(json.dumps(result,indent=2)+"\n")
    for t in range(4):
        if bestsc==[100]*3: break
        relaxed=t%2==0
        # After a relaxed step, restore the two exact projections in the next window.
        nfree=65+5*((a.shard+t)%2)
        free=window(current,rng,nfree,(a.shard+t)%2)
        target=[97,97,91] if relaxed else [100,100,max(92,sorted(bestsc)[0]+1)]
        stat,out,sc=solve(current,free,target,a.seconds,rng.randrange(1,2**30),relaxed)
        events.append({"round":t,"free":free,"target":target,"solver":stat,"scores":sc})
        print(json.dumps(events[-1]),flush=True)
        if out is not None:
            current=out
            if record_key(sc)>record_key(bestsc):
                best,bestsc=out,sc
            if sc==[100]*3:
                best,bestsc=out,sc
        elif not relaxed:
            current=best
        save()
    save()
if __name__=="__main__": main()
