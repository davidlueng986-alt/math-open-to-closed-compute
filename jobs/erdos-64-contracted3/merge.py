#!/usr/bin/env python3
"""Validate each constrained family, shard boundaries and survivor totals."""
import json,os,sys
from pathlib import Path
from collections import defaultdict
root,out=map(Path,sys.argv[1:3]);k=int(os.environ['SHARDS'])
expected={16:4060,18:41301}
stats=defaultdict(lambda:defaultdict(int));witnesses=[];overflow=0
for i in range(k):
    p=root/f'shard-{i}'/'result.json'
    if not p.is_file():raise RuntimeError(f'missing shard {i}')
    d=json.loads(p.read_text())
    if d['shard']!=i or d['shards']!=k or d['problem']!='ERDOS-64':
        raise RuntimeError(f'shard identifier mismatch {i}')
    for n,vals in d['statistics'].items():
        for key,val in vals.items():stats[int(n)][key]+=val
    witnesses.extend(d['witnesses'])
    overflow+=d['witness_overflow']
for n,v in expected.items():
    s=stats[n]
    if s['base_graphs']!=v:raise RuntimeError(f'base census mismatch n={n}: {s["base_graphs"]} != {v}')
    if s['skipped_triangle_edges']+s['triangle_free_contraction_edges']!=s['base_graphs']*(3*n//2):
        raise RuntimeError(f'edge audit failed n={n}')
    if s['excluded_by_monodromy']+s['exact_checked']!=s['voltage_assignments_total']:
        raise RuntimeError(f'monodromy/full-oracle coverage mismatch n={n}')
    if s['exact_unknown']>s['exact_checked']:raise RuntimeError('unknown count invalid')
result={'problem':'ERDOS-64','original_problem':'OPEN',
    'complete_census_of_restricted_family':True,
    'scope':'C3 covers of contracted cubic base graphs from order 16,18 only; one degree4 vertex per base',
    'witness_candidates':witnesses,
    'additional_witnesses_in_artifacts':overflow,
    'exact_unknown':sum(v['exact_unknown'] for v in stats.values()),
    'restricted_family_absence_certified':not witnesses and overflow==0 and all(v['exact_unknown']==0 for v in stats.values()),
    'counts':{str(n):dict(v) for n,v in stats.items()},
    'warning':'No inference for general graphs; see exact restricted-family scope.'}
out.mkdir(parents=True,exist_ok=True)
(out/'contracted3_census.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print('Complete restricted base census; witnesses',len(witnesses)+overflow,'unknown',result['exact_unknown'])
