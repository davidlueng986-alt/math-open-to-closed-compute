import itertools,json,sys
from pathlib import Path
def verify(rows):
    assert len(rows)==100 and all(len(r)==5 and all(0<=v<10 for v in r) for r in rows)
    assert all(len({(r[i],r[j]) for r in rows})==100 for i,j in itertools.combinations(range(5),2))
def parse(path):
    lines=path.read_text().strip().splitlines()
    if lines[0]=="SAT_WITNESS":
        rows=[list(map(int,l.split())) for l in lines[1:]]
        verify(rows)
        return {"status":"SAT_WITNESS","points":rows}
    assert len(lines)==1
    tok=lines[0].split()
    return {tok[i]:int(tok[i+1]) for i in range(0,len(tok),2)}
if __name__=="__main__":
    s,n,p=int(sys.argv[1]),int(sys.argv[2]),Path(sys.argv[3])
    exact=parse(p/"exact.txt"); h=parse(p/"heuristic.txt")
    if exact.get("status")!="SAT_WITNESS":
        assert exact["total_representatives"]==21824
        assert sum(exact[k] for k in ("repeated_two_pairs","duplicate_four_agree","rank_filter","csp_unsat","unknown"))==exact["shard_cases"]
    if h.get("status")!="SAT_WITNESS": assert h["viable"]==h["closed"]+h["unknown"]
    unknown=[l.split()[-1] for l in (p/"heuristic.log").read_text().splitlines() if l.startswith("UNKNOWN_STACK ")]
    assert all(len(t)==500 and set(t)<=set("01234") for t in unknown)
    (p/"result.json").write_text(json.dumps({"shard":s,"shards":n,"exact":exact,"heuristic":h,"unknown_stacks":unknown},indent=2)+"\n")
