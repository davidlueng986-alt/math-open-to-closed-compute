#!/usr/bin/env python3
"""Check zero-solve checkpoint restoration, including already split OPEN trees."""
import argparse,json
from pathlib import Path
def check(old,new,expect='certified'):
 assert expect in ('certified','open')
 assert old.resolve()!=new.resolve(), 'Resume source and output must differ'
 a=json.loads((old/'checkpoint.json').read_text())
 b=json.loads((new/'checkpoint.json').read_text())
 assert a['task']==b['task'] and a['base_sha256']==b['base_sha256']
 status='ALL_CUBES_CERTIFIED_UNSAT_PENDING_ENCODING_AUDIT' if expect=='certified' else 'OPEN'
 assert a['status']==b['status']==status, 'Unexpected restored checkpoint state'
 assert all(n['status']!='VERIFIED_WITNESS' for n in a['nodes'].values()), 'Witnesses require their own independent replay'
 if expect=='open':
  assert any(n['status']=='SPLIT' for n in a['nodes'].values()), 'OPEN gate must exercise a real split tree'
  assert any(n['status'] in ('OPEN','UNSAT_UNCERTIFIED') for n in a['nodes'].values())
 assert a['models']==b['models'] and a['cuts']<=b['cuts']
 assert a['nodes']==b['nodes'], 'Resume must preserve all nodes, proof identities and attempt counts'
 assert (new/'cuts.jsonl').read_bytes().startswith((old/'cuts.jsonl').read_bytes()), 'Resume lost or reordered saved cuts'
 replayed=0
 for k,n in a['nodes'].items():
  if n['status']=='CERTIFIED_UNSAT':
   log=new/'proofs'/k/'resume-check.log'
   assert log.exists() and 's VERIFIED' in log.read_text(errors='replace'), 'Saved proof was not replayed'
   replayed+=1
 print(json.dumps(dict(status='REAL_CHECKPOINT_RESUME_VERIFIED',expected_state=expect,task=a['task']['id'],cuts=b['cuts'],terminals=b['terminal_counts'],replayed_proofs=replayed)),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('old',type=Path);p.add_argument('new',type=Path)
 p.add_argument('--expect',choices=('certified','open'),default='certified')
 a=p.parse_args();check(a.old,a.new,a.expect)

