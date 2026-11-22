#!/usr/bin/env python3
"""Fail if an enumerated cubic graph or voltage assignment is unaccounted for."""
import json,os,sys
from pathlib import Path
from collections import defaultdict

def main():
    shards=Path(sys.argv[1]);out=Path(sys.argv[2])
    count=int(os.environ['SHARDS'])
    expected={4:1,6:2,8:5,10:19,12:85,14:509,16:4060,18:41301,20:510489}
    sums=defaultdict(lambda:defaultdict(int))
    hits=[];unknown=0;overflow=0
    for i in range(count):
        path=shards/f'shard-{i}'/'result.json'
        if not path.is_file():raise RuntimeError(f'missing shard {i}')
        d=json.loads(path.read_text())
        if d['shard']!=i or d['shards']!=count or d['problem']!='ERDOS-64':
            raise RuntimeError(f'identity mismatch shard {i}')
        for n,variants in d['statistics'].items():
            for m,st in variants.items():
                for k,v in st.items():sums[n,m][k]+=v
        unknown+=d['unknown_cutoffs']
        hits+=d['witnesses']
        overflow+=d['witness_overflow']
    for n,c in expected.items():
        for m in range(2,64//n+1):
            if not (41<=n*m<=63):continue
            s=sums[str(n),str(m)]
            if s['base_graphs']!=c:
                raise RuntimeError(f'nauty census incomplete: n={n} m={m} got={s["base_graphs"]} expected={c}')
            if s['assignments_total']!=s['excluded_by_base_cycles']+s['checked_survivors']:
                raise RuntimeError(f'voltage coverage incomplete n={n},m={m}')
            if s['unknown_cutoffs']>s['checked_survivors']:
                raise RuntimeError('impossible timeout count')
    result={'problem':'ERDOS-64','scope':'connected cubic base order <=20; cyclic covers of order 41..63',
            'complete_base_census':True,'original_problem':'OPEN',
            'finite_family_excluded':not hits and not overflow and unknown==0,
            'independent_verification_needed':bool(hits or overflow or unknown),
            'witness_candidates':hits,'additional_witnesses_in_shard_artifacts':overflow,
            'unknown_cycle_check_cutoffs':unknown,
            'families':{f'{n}x{m}':dict(st) for (n,m),st in sums.items()},
            'caution':'This computation does not establish the general Erdős–Gyárfás conjecture.'}
    out.mkdir(exist_ok=True,parents=True)
    (out/'cyclic_covers.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('base census complete; witness candidates',len(hits)+overflow,'unknowns',unknown,
          'family-excluded',result['finite_family_excluded'])

if __name__=='__main__':main()
