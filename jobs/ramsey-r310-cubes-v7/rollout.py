#!/usr/bin/env python3
"""All remaining D678 bands, exactly covered by the v7 checkpoint worker.
The existing D6-N9-B3 pilot is deliberately not duplicated."""
import argparse,json
from pathlib import Path
from plan import make,save,sha
def build(cert,prior):
 bands=json.loads(Path(prior).read_text())
 assert len(bands)==48
 assert len({(b['d'],b['q'],b['band']) for b in bands})==48
 empty=[b for b in bands if b['new_count']==0]
 assert {(b['d'],b['q'],b['band']) for b in empty}=={(6,6,0),(6,7,0),(7,6,0),(8,6,0)}
 pilot=next(b for b in bands if (b['d'],b['q'],b['band'])==(6,9,3))
 selected=[b for b in bands if b['new_count'] and b!=pilot]
 assert len(selected)==43
 tasks=[]; summaries=[]
 for b in selected:
  # Exact edge count m; split cross-edge counts in half for narrower
  # profile bands. Large bands can further split adaptively in each worker.
  part=2 if b['new_count']<=70 else 1
  result=make(cert,prior,b['d'],b['q'],b['band'],10000,part)
  assert result['parent']==b and result['profiles']==b['new_count']
  tasks.extend(result['tasks'])
  summaries.append(dict(parent=b['d'],q=b['q'],band=b['band'],profiles=result['profiles'],coverage_pairs=result['coverage_pairs'],tasks=len(result['tasks'])))
 assert 0<len(tasks)<=256 and len({t['id'] for t in tasks})==len(tasks)
 assert all(t['key']==sha({k:v for k,v in t.items() if k!='key'}) for t in tasks)
 return dict(schema=1,engine='v7',omitted_empty_bands=empty,existing_pilot=pilot,band_count=len(selected),summaries=summaries,tasks=tasks)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--cert',required=True);p.add_argument('--prior',required=True);p.add_argument('--out',required=True)
 a=p.parse_args();x=build(a.cert,a.prior);save(a.out,x)
 print(json.dumps(dict(status='EXACT_ROLLOUT_COVERAGE_VERIFIED',bands=x['band_count'],tasks=len(x['tasks']),empty=len(x['omitted_empty_bands']),existing_pilot=x['existing_pilot']),separators=(',',':')),flush=True)
