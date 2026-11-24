#!/usr/bin/env python3
"""Collect audited checkpoints; a bounded unfinished job is not a negative answer."""
import argparse, hashlib, json, pathlib, shutil, sys

def main():
 p=argparse.ArgumentParser();p.add_argument('--artifacts',default='artifacts');p.add_argument('--out',default='summary');a=p.parse_args()
 source=pathlib.Path(a.artifacts);target=pathlib.Path(a.out);target.mkdir(parents=True,exist_ok=True)
 expected=[1,2,6,8,9,10];rows=[];witnesses=[]
 compute_root=pathlib.Path(__file__).resolve().parents[1]
 sys.path.insert(0,str(compute_root/'mols10-e077-exact'))
 from encode import verify_squares
 for i in expected:
  state=source/f'exact-{i}'/'state';entry={'shard':i,'present':state.exists()}
  if (state/'verification.json').is_file():
   entry['verified_summary']=json.loads((state/'verification.json').read_text())
  if (state/'queue.json').is_file():
   q=json.loads((state/'queue.json').read_text());entry['task_status']=q['task_status'];entry['base_cnf_sha256']=q['base_cnf_sha256']
   entry['leaf_status_counts']={}
   for node in q['nodes'].values():
    if node['status']!='SPLIT':entry['leaf_status_counts'][node['status']]=entry['leaf_status_counts'].get(node['status'],0)+1
    if node['status']=='SAT_VERIFIED':
     evidence=state/node['evidence'];r=json.loads(evidence.read_text());w=json.loads((evidence.parent/r['witness']).read_text())
     verify_squares(w['squares']);assert len(w['squares'])==3 and len(w['squares'][0])==10
     witnesses.append({'route':'exact','shard':i,'squares':w['squares']})
  rows.append(entry)
 constructors=[]
 for seed in range(770101,770105):
  folder=source/f'construct-{seed}';entry={'seed':seed,'present':folder.exists()}
  if (folder/'checkpoint.json').is_file():
   c=json.loads((folder/'checkpoint.json').read_text());entry.update(status=c['status'],iterations=c['iterations'],evaluated_pairs=c['evaluated_pairs'],best_packing=c['best']['packing'],common_transversals=c['best']['common_transversals'])
   if c['status']=='YES_WITNESS':
    ss=[[c['best'][label][10*r:10*r+10] for r in range(10)] for label in ('A','B','C')]
    verify_squares(ss);witnesses.append({'route':'construction','seed':seed,'squares':ss})
  constructors.append(entry)
 exhausted=all(row.get('verified_summary',{}).get('task_status')=='SHARD_EXHAUSTED_WITH_CERTIFICATES' for row in rows)
 status='VERIFIED_YES_WITNESS' if witnesses else 'ALL_SIX_SHARDS_CERTIFIED_REQUIRES_FINAL_GLOBAL_AUDIT' if exhausted else '未完成任務'
 summary={'problem':'MOLS10-3','task_status':status,'exact':rows,'construction':constructors,'witnesses':witnesses,'global_nonexistence_claim':False,
   'coverage':'Six simultaneous-even canonical cycle shards; 31 centralizer first-pair representatives. Missing and unresolved leaves remain explicit.',
   'resume':'Download the corresponding exact-N or construct-SEED artifact and resume its saved state. Solver learned clauses are not retained; construction resumes population/RNG.'}
 (target/'summary.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
 # Preserve small checkpoint metadata and concrete candidates on the results branch.
 # Complete CNFs and proofs remain in the per-job artifacts; none is silently dropped
 # from a supposedly replayable certificate directory.
 for folder in source.iterdir():
  if not folder.is_dir():continue
  dest=target/'checkpoints'/folder.name
  for path in folder.rglob('*'):
   if path.is_file() and path.suffix in {'.json','.jsonl','.txt','.log'} and path.stat().st_size<4*1024*1024:
    to=dest/path.relative_to(folder);to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(path,to)
 print(json.dumps(summary,ensure_ascii=False))
if __name__=='__main__':main()
