#!/usr/bin/env python3
"""Audit nauty census and exact cut-vertex witness coverage."""
import json,os,sys
from pathlib import Path
from collections import defaultdict
root,out=map(Path,sys.argv[1:3]);shards=int(os.environ['SHARDS'])
expected={20:510489,22:7319447,24:117940535}
total=defaultdict(lambda:defaultdict(int));witnesses=[]
for i in range(shards):
    p=root/f"shard-{i}"/"result.json"
    if not p.is_file():raise RuntimeError(f"missing shard {i}")
    d=json.loads(p.read_text())
    if (d["shard"],d["shards"],d["problem"])!=(i,shards,"ERDOS-64"):
        raise RuntimeError("shard metadata invalid")
    for k,values in d["statistics"].items():
        for key,num in values.items():total[int(k)][key]+=num
    if d["total_witnesses"]!=len(d["witnesses"]):
        raise RuntimeError(f"bad witness count in {i}")
    witnesses.extend(d["witnesses"])
for n,v in expected.items():
    s=total[n]
    if s["base_graphs"]!=v:raise RuntimeError(f"incomplete graph census for {n}: got {s['base_graphs']} expected {v}")
    if not (s["base_graphs"]>=s["survive_4_8"]>=s["survive_4_8_3_7_16"]>=0):
        raise RuntimeError("invalid stage monotonicity")
    if s["witnesses"]!=s["subdivision_candidates"]:
        raise RuntimeError("candidate count != number of full verified witness graphs")
result={"problem":"ERDOS-64","full_problem_status":"OPEN",
        "restricted_search_complete":True,"family_excluded":not witnesses,
        "scope":"All cubic edge-subdivision two-block graphs derived from connected cubic base order 20,22,24",
        "count_by_base_order":{str(n):dict(v) for n,v in total.items()},
        "witnesses":witnesses,"warning":"Does not cover noncubic base graphs, cutvertex designs beyond this exact construction, or biconnected arbitrary graphs."}
out.mkdir(exist_ok=True,parents=True)
(out/"cutvertex_census.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
print("complete 20/22/24 cubic base census; witnesses",len(witnesses))
