#!/usr/bin/env python3
import os,sys,json
from pathlib import Path
root,out=map(Path,sys.argv[1:3])
assert int(os.environ["SHARDS"])==8
cases=[];w=[]
for i in range(8):
    d=json.loads((root/f"shard-{i}"/"result.json").read_text())
    assert (d["problem"],d["shard"],d["shards"],d["target"]["n"])==("ERDOS-64",i,8,21+i)
    assert d["control"]["status"]=="SAT_INDEPENDENTLY_CHECKED"
    assert (d["target"]["status"]=="SAT_INDEPENDENTLY_CHECKED")==(d["witness"] is not None)
    cases.append(d["target"])
    if d["witness"]:w.append(d["witness"])
out.mkdir(exist_ok=True,parents=True)
(out/"one_defect_minimal.json").write_text(json.dumps({"problem":"ERDOS-64","scope":"minimum-order/size one-defect candidate branch, n=21..28, invariant structural constraints","cases":cases,"witnesses":w,"note":"solver UNSAT and timeout not global proof; independently check any SAT witness and Lean formalize"},indent=2)+"\n")
print([(x["n"],x["status"]) for x in cases],"witnesses",len(w))
