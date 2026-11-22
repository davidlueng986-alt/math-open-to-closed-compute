#!/usr/bin/env python3
"""Check exact restricted two-terminal gadget census and preserve every witness."""
import os,sys,json
from pathlib import Path
from collections import defaultdict
base,out=map(Path,sys.argv[1:3]);N=int(os.environ['SHARDS'])
expected={20:510489,22:7319447,24:117940535}
tot=defaultdict(lambda:defaultdict(int));witnesses=[]
for shard in range(N):
    p=base/f"shard-{shard}"/"result.json"
    if not p.is_file():raise RuntimeError("missing shard "+str(shard))
    r=json.loads(p.read_text())
    if (r['shard'],r['shards'],r['problem'])!=(shard,N,'ERDOS-64'):
        raise RuntimeError(f"shard mismatch {shard}")
    for n,values in r['statistics'].items():
        for key,val in values.items():tot[int(n)][key]+=val
    if r['witness_count']!=len(r['witnesses']):raise RuntimeError(f"truncated witnesses shard {shard}")
    witnesses+=r['witnesses']
for n,count in expected.items():
    s=tot[n]
    if s['base_graphs']!=count:raise RuntimeError(f"not complete n={n}: {s['base_graphs']} vs {count}")
    if not (0<=s['ring_witnesses']<=s['connected_twoport_edge_candidates']):
        raise RuntimeError(f"impossible candidate count n={n}")
    if not (s['base_graphs']>=s['after_C4_C8_edge_intersection']>=s['after_C16_intersection']>=0):
        raise RuntimeError(f"stage count nonmonotonic n={n}")
if sum(v['ring_witnesses'] for v in tot.values())!=len(witnesses):
    raise RuntimeError("witness count does not match merge")
res={"problem":"ERDOS-64","original_status":"OPEN unless a witness independently proves NO",
     "family_census_complete":True,
     "scope":"every connected cubic F of order20,22,24, every edge e, K=F-e with no C4,C8,C16; all ring lengths 2..128",
     "statistics":{str(n):dict(x) for n,x in tot.items()},
     "counterexample_candidates":witnesses,
     "any_full_no_witness":bool(witnesses),
     "warning":"NO candidate implies only no witness within this bounded family and ring lengths; not original YES."}
out.mkdir(exist_ok=True,parents=True)
(out/"twoport_ring.json").write_text(json.dumps(res,indent=2,sort_keys=True)+"\n")
print("complete restricted census; original-NO candidates:",len(witnesses))
