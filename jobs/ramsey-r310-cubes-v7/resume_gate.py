#!/usr/bin/env python3
"""Check real cross-run restored checkpoints, not merely the new solver result."""
import argparse,json
from pathlib import Path
def check(old,new):
 a=json.loads((old/'checkpoint.json').read_text())
 b=json.loads((new/'checkpoint.json').read_text())
 assert a['task']==b['task'] and a['base_sha256']==b['base_sha256']
 assert a['status']==b['status']=='ALL_CUBES_CERTIFIED_UNSAT_PENDING_ENCODING_AUDIT'
 assert a['models']==b['models'] and a['cuts']<=b['cuts']
 assert a['nodes']==b['nodes'], 'Resume must preserve all proof identities and attempt counts'
 assert (new/'cuts.jsonl').read_bytes().startswith((old/'cuts.jsonl').read_bytes())
 for k,n in a['nodes'].items():
  if n['status']=='CERTIFIED_UNSAT':
   log=new/'proofs'/k/'resume-check.log'
   assert log.exists() and 's VERIFIED' in log.read_text(errors='replace')
 print(json.dumps(dict(status='REAL_CHECKPOINT_RESUME_VERIFIED',task=a['task']['id'],cuts=b['cuts'],terminals=b['terminal_counts'])),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('old',type=Path);p.add_argument('new',type=Path);a=p.parse_args();check(a.old,a.new)
