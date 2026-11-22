#!/usr/bin/env python3
"""Merge finite SAT attempts without treating uncertified UNSAT as a proof."""
import json,os,sys
from pathlib import Path
root,out=map(Path,sys.argv[1:3]);N=int(os.environ["SHARDS"])
if N!=2:raise RuntimeError("expected 2 direct SAT test shards")
cases=[]
for i,n in enumerate((41,43)):
 p=root/f"shard-{i}"/"result.json"
 if not p.is_file():raise RuntimeError(f"missing shard {i}")
 d=json.loads(p.read_text())
 if (d["shard"],d["shards"],d["problem"],d["target"]["n"])!=(i,N,"ERDOS-64",n):
  raise RuntimeError(f"SAT metadata mismatch {i}")
 if d["control"]["status"]!="SAT_UNVERIFIED":raise RuntimeError(f"positive control failed {i}")
 cases.append(d["target"])
result={"problem":"ERDOS-64","original_status":"OPEN",
 "type":"direct SAT counterexample search in exactly one-degree-four rest-cubic class",
 "cases":cases,"positive_controls_passed":True,"complete_execution":True,
 "potential_witnesses_require_independent_verification":[x["n"] for x in cases if x["status"]=="SAT_UNVERIFIED"],
 "unknown_or_timeout":[x["n"] for x in cases if x["status"] not in ("SAT_UNVERIFIED","UNSAT_SOLVER_REPORTED")],
 "caution":"These are solver reports, not certified UNSAT/Lean or a universal statement. Zero SAT models for n41/n43 cannot settle original."}
out.mkdir(exist_ok=True,parents=True)
(out/"sms_direct.json").write_text(json.dumps(result,indent=2)+"\n")
print("direct SAT n41/43 reports",[(x["n"],x["status"]) for x in cases])
