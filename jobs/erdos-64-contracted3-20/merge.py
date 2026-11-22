#!/usr/bin/env python3
"""Audit every F20 connected-cubic edge, all voltages and exact C3 cover tests."""
import os,json,sys
from pathlib import Path
from collections import defaultdict
root,out=map(Path,sys.argv[1:3]);shards=int(os.environ['SHARDS'])
expect=510489; n=20
total=defaultdict(int);witnesses=[];overflow=0
for i in range(shards):
    p=root/f'shard-{i}'/'result.json'
    if not p.is_file():raise RuntimeError(f'missing shard {i}')
    d=json.loads(p.read_text())
    if d['problem']!='ERDOS-64' or d['shard']!=i or d['shards']!=shards:
        raise RuntimeError(f'shard metadata mismatch {i}')
    st=d['statistics']
    if set(st)!={'20'}:raise RuntimeError('unexpected base order')
    for k,v in st['20'].items():total[k]+=v
    witnesses.extend(d['witnesses'])
    overflow+=d['witness_overflow']
if total['base_graphs']!=expect:
    raise RuntimeError(f'incomplete nonisomorphic cubic F20 census {total["base_graphs"]}/{expect}')
if total['triangle_free_contraction_edges']+total['skipped_triangle_edges']!=expect*30:
    raise RuntimeError('incomplete edge contraction coverage')
if (total['excluded_by_triple']+total['excluded_by_monodromy']+total['exact_checked']
    !=total['voltage_assignments_total']):
    raise RuntimeError('not all voltages mathematically or exactly checked')
if total['exact_unknown']>total['exact_checked']:
    raise RuntimeError('exact checker unknown count invalid')
result={
 'problem':'ERDOS-64','original_problem':'OPEN',
 'scope':'All C3 regular voltage covers of every simple one-edge contraction of a connected cubic graph on 20 vertices; noncubic cover on 57 vertices',
 'restricted_family_census_complete':True,
 'restricted_family_excluded':not witnesses and not overflow and total['exact_unknown']==0,
 'unknown_exact_oracle_cases':total['exact_unknown'],
 'witness_candidates':witnesses,
 'witness_overflow_in_shard_artifacts':overflow,
 'statistics':dict(total),
 'note':'All restrictions are explicit. No inference for arbitrary min-degree-3 graphs.'
}
out.mkdir(exist_ok=True,parents=True)
(out/'contracted3_20.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print('Base census verified; witness',len(witnesses)+overflow,'unknown',total['exact_unknown'])
