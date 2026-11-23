import json,sys
from pathlib import Path
from search import scores,record_key
src,dst=map(Path,sys.argv[1:])
results=[]
for d in sorted(src.glob("shard-*")):
    p=d/"result.json"
    if not p.exists(): continue
    r=json.loads(p.read_text())
    assert r["positive_control"]=="PASS"
    assert scores(r["best_squares"])==r["best_scores"]
    results.append(r)
assert results,"no valid shard results"
best=max(results,key=lambda r:record_key(r["best_scores"]))
out={"problem":"MOLS10-3","status":"YES_WITNESS" if best["best_scores"]==[100]*3 else "OPEN","best_scores":best["best_scores"],"best_squares":best["best_squares"],"shards_checked":len(results),"rounds":sum(len(x["events"]) for x in results),"scope":"constructive LNS only; no global NO conclusion"}
(dst/"mols10_best.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({k:v for k,v in out.items() if k!="best_squares"}))
