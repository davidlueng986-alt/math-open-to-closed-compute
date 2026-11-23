import json,sys
from pathlib import Path
from summarize import verify
src,dst=map(Path,sys.argv[1:])
rows=[json.loads(p.read_text()) for p in src.glob("shard-*/result.json")]
assert len(rows)==4 and {r["shard"] for r in rows}==set(range(4))
witnesses=[r[k]["points"] for r in rows for k in ("exact","heuristic") if r[k].get("status")=="SAT_WITNESS"]
for w in witnesses:verify(w)
ex={}
if not any(r["exact"].get("status")=="SAT_WITNESS" for r in rows):
    keys=("shard_cases","repeated_two_pairs","duplicate_four_agree","rank_filter","csp_unsat","unknown","nodes")
    ex={k:sum(r["exact"][k] for r in rows) for k in keys}
    assert ex["shard_cases"]==21824
    assert sum(ex[k] for k in keys[1:6])==ex["shard_cases"]
    if ex["unknown"]==0: assert [ex[k] for k in keys[1:5]]==[31,570,18006,3217]
h={k:sum(r["heuristic"].get(k,0) for r in rows) for k in ("tested","viable","closed","unknown","nodes")}
unknown=list(dict.fromkeys(t for r in rows for t in r["unknown_stacks"]))
out={"problem":"MOLS10-3","status":"YES_WITNESS" if witnesses else "OPEN","restricted_coset_census":ex,"heuristic_totals":h,"sat_witnesses":witnesses,"unknown_stacks":unknown}
(dst/"coarse_lift_summary.json").write_text(json.dumps(out,indent=2)+"\n")
print({k:v for k,v in out.items() if k not in ("unknown_stacks","sat_witnesses")})
