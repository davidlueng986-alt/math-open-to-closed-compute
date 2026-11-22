#!/usr/bin/env python3
"""Audit complete enumeration of a restricted family, never the whole Erdős #64."""
from collections import defaultdict
import json,os,sys
from pathlib import Path
def main():
 root,out=map(Path,sys.argv[1:3]);shards=int(os.environ['SHARDS'])
 expected={14:509,16:4060,18:41301,20:510489}
 counts=defaultdict(lambda:defaultdict(int));witness=[];overflow=0;unknown=0
 for i in range(shards):
  f=root/f'shard-{i}'/'result.json'
  if not f.is_file():raise RuntimeError(f'missing shard {i}')
  d=json.loads(f.read_text())
  if (d['shard'],d['shards'],d['problem'])!=(i,shards,'ERDOS-64'):
   raise RuntimeError('mismatched shard metadata')
  for n,st in d['statistics'].items():
   for k,v in st.items():counts[int(n)][k]+=v
  witness.extend(d['witnesses']);overflow+=d['witness_overflow'];unknown+=d['unknown_cutoffs']
 for n,expected_count in expected.items():
  s=counts[n]
  if s['base_graphs']!=expected_count:
   raise RuntimeError(f'incomplete graph census for n={n}: {s["base_graphs"]} instead of {expected_count}')
  if s['biconnected_bases']+s['excluded_nonbiconnected']!=expected_count:
   raise RuntimeError('wrong biconnectivity census')
  if s['excluded_by_monodromy']+s['verified_survivors']!=s['voltage_assignments_total']:
   raise RuntimeError('voltage cover counts inconsistent')
  if s['unknown_cutoffs']>s['verified_survivors']:
   raise RuntimeError('impossible cutoff count')
 result={'problem':'ERDOS-64',
  'mathematical_status':'OPEN',
  'scope':'all degree-3 S3 permutation covers of biconnected cubic base graphs of order 14,16,18,20',
  'base_graph_census_complete':True,
  'restricted_family_absence_certified':not witness and overflow==0 and unknown==0,
  'unknown_exact_check_cutoffs':unknown,
  'witness_candidates':witness,
  'additional_witnesses_in_artifacts':overflow,
  'statistics':{n:dict(s) for n,s in counts.items()},
  'caution':'Does NOT cover nonbiconnected bases, more layers, unequal vertex degrees, or arbitrary finite graphs; not a universal proof.'}
 out.mkdir(exist_ok=True,parents=True)
 (out/'s3_bicon.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(f"S3 bicon connected cubic base census OK; witnesses={len(witness)+overflow}; cutoffs={unknown}")
if __name__=='__main__':main()
