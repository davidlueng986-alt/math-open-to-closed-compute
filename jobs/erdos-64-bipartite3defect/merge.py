#!/usr/bin/env python3
import json,os,sys
from pathlib import Path
root,out=map(Path,sys.argv[1:3])
if int(os.environ["SHARDS"])!=4:raise ValueError("wrong shard count")
cases=[];witness=[]
for i,n in enumerate((21,23,25,27)):
    f=root/f"shard-{i}"/"result.json"
    if not f.is_file():raise RuntimeError(f"missing shard {i}")
    d=json.loads(f.read_text())
    if (d["problem"],d["shard"],d["shards"],d["target"]["n"])!=("ERDOS-64",i,4,n):raise ValueError("wrong shard metadata")
    if d["control"]["status"]!="SAT_INDEPENDENTLY_CHECKED":raise ValueError("positive control failed")
    if (d["target"]["status"]=="SAT_INDEPENDENTLY_CHECKED")!=(d["witness"] is not None):raise ValueError("witness accounting failed")
    cases.append(d["target"])
    if d["witness"] is not None:witness.append(d["witness"])
result={"problem":"ERDOS-64","scope":"connected bipartite graphs of order 21,23,25,27, with exactly three degree2 vertices and all others degree3",
"cases":cases,"witnesses":witness,"positive_controls_passed":True,
"note":"SAT witnesses must be audited and Lean-formalized; UNSAT or timeout of this family is not a proof of the original conjecture."}
out.mkdir(exist_ok=True,parents=True)
(out/"bipartite3defect.json").write_text(json.dumps(result,indent=2)+"\n")
print([(x["n"],x["status"]) for x in cases],"witnesses",len(witness))
