#!/usr/bin/env python3
"""Collect audited checkpoints; a bounded unfinished job is not a negative answer."""
import argparse, hashlib, json, pathlib, shutil, sys

def file_sha256(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()

def main():
 p=argparse.ArgumentParser();p.add_argument('--artifacts',default='artifacts');p.add_argument('--out',default='summary');a=p.parse_args()
 source=pathlib.Path(a.artifacts);target=pathlib.Path(a.out);target.mkdir(parents=True,exist_ok=True)
 rows=[];witnesses=[]
 compute_root=pathlib.Path(__file__).resolve().parents[1]
 sys.path.insert(0,str(compute_root/'mols10-e077-exact'))
 from encode import verify_squares
 manifest_path=compute_root/'mols10-e077-exact'/'coverage.json'
 manifest=json.loads(manifest_path.read_text())
 resume_manifest_path=pathlib.Path(__file__).with_name('resume_manifest.json')
 resume_manifest=json.loads(resume_manifest_path.read_text())
 resume_rows={row['shard']:row for row in resume_manifest['shards']}
 assert resume_manifest['source_run_id']==45301881745
 expected_rows={row['shard']:row for row in manifest['required_shards']}
 expected=sorted(expected_rows)
 assert expected==[1,2,6,8,9,10] and len(manifest['required_shards'])==6
 assert manifest['n']==10 and manifest['squares']==3 and manifest['even_row_normalization'] is True
 for i in expected:
  state=source/f'exact-{i}'/'state';entry={'shard':i,'present':state.exists()}
  entry['verification_source']='Cached per-shard replay record; the collector does not replay LRAT certificates.'
  if (state/'verification.json').is_file():
   entry['verified_summary']=json.loads((state/'verification.json').read_text())
  if (state/'replay_status.json').is_file():
   entry['replay_status']=json.loads((state/'replay_status.json').read_text())
  if (state/'queue.json').is_file():
   q=json.loads((state/'queue.json').read_text());entry['task_status']=q['task_status'];entry['base_cnf_sha256']=q['base_cnf_sha256']
   identity_errors=[]
   for key,want in [('shard',i),('n',10),('squares',3),('parts',expected_rows[i]['parts']),('even_row_normalization',True)]:
    if q.get(key)!=want:identity_errors.append(f'queue {key} does not match required shard')
   if q.get('base_cnf_sha256')!=expected_rows[i]['cnf_sha256']:identity_errors.append('queue CNF hash does not match required manifest')
   for filename,key in [('base.cnf','base_cnf_sha256'),('mapping.json','mapping_sha256')]:
    if not (state/filename).is_file():identity_errors.append(f'missing {filename}')
    elif file_sha256(state/filename)!=q.get(key):identity_errors.append(f'{filename} bytes do not match queue hash')
   queue_digest=file_sha256(state/'queue.json')
   entry['queue_sha256']=queue_digest;entry['identity_errors']=identity_errors
   entry['leaf_status_counts']={}
   for node in q['nodes'].values():
    if node['status']!='SPLIT':entry['leaf_status_counts'][node['status']]=entry['leaf_status_counts'].get(node['status'],0)+1
    if node['status']=='SAT_VERIFIED':
     evidence=state/node['evidence'];r=json.loads(evidence.read_text());w=json.loads((evidence.parent/r['witness']).read_text())
     verify_squares(w['squares']);assert len(w['squares'])==3 and len(w['squares'][0])==10
     witnesses.append({'route':'exact','shard':i,'squares':w['squares']})
   cached=entry.get('verified_summary',{});binding=cached.get('record_binding',{})
   expected_binding={'queue_sha256':queue_digest,'base_cnf_sha256':q.get('base_cnf_sha256'),
                     'mapping_sha256':q.get('mapping_sha256'),'shard':i,'n':10,'squares':3,
                     'parts':expected_rows[i]['parts'],'even_row_normalization':True,'verify_returncode':0}
   binding_errors=[f'cached binding mismatch: {key}' for key,value in expected_binding.items() if binding.get(key)!=value]
   if cached.get('coverage_tree_verified') is not True:binding_errors.append('cached record does not confirm coverage-tree verification')
   if cached.get('leaf_status_counts')!=entry['leaf_status_counts']:binding_errors.append('cached leaf counts do not match current queue')
   if cached.get('task_status')!=q.get('task_status'):binding_errors.append('cached task status does not match current queue')
   if cached.get('lrat_certificates_replayed')!=entry['leaf_status_counts'].get('UNSAT_VERIFIED',0):binding_errors.append('cached replay count does not match certified leaf count')
   replay_status=entry.get('replay_status',{}).get('status')
   if replay_status and replay_status!='VERIFIED_CURRENT_STATE':binding_errors.append('latest replay is pending or failed')
   entry['cached_verification_binding']={'valid':not identity_errors and not binding_errors,'errors':identity_errors+binding_errors}
  origin_path=state.parent/'resume_source.json';preservation_path=state.parent/'preservation.json'
  origin=json.loads(origin_path.read_text()) if origin_path.is_file() else {}
  preservation=json.loads(preservation_path.read_text()) if preservation_path.is_file() else {}
  required=resume_rows[i];required_count=len(required['certified_nodes'])
  source_checks=[
   (origin.get('status')=='SOURCE_IDENTITY_VERIFIED','source identity was not verified'),
   (origin.get('source_run_id')==45301881745 and origin.get('shard')==i,'source run/shard differs'),
   (origin.get('source_queue_sha256')==required['source_queue_sha256'],'source queue hash differs'),
   (origin.get('source_manifest_sha256')==file_sha256(resume_manifest_path),'source manifest hash differs'),
   (origin.get('imported_certified_count')==required_count,'imported certificate count differs'),
   (preservation.get('status')=='IMPORTED_CERTIFICATES_PRESERVED','imported certificates were not preserved'),
   (preservation.get('source_run_id')==45301881745 and preservation.get('shard')==i,'preservation run/shard differs'),
   (preservation.get('source_manifest_sha256')==file_sha256(resume_manifest_path),'preservation manifest differs'),
   (preservation.get('current_queue_sha256')==entry.get('queue_sha256'),'preservation record is stale'),
   (preservation.get('preserved_count')==required_count,'preserved certificate count differs'),
   (set(preservation.get('node_statuses',{}))==set(required['certified_nodes']),'preserved node set differs')]
  source_errors=[message for valid,message in source_checks if not valid]
  entry['resume_source_validation']={'valid':not source_errors,'errors':source_errors,
    'source_run_id':45301881745,'expected_imported_certificates':required_count,
    'preservation':preservation}
  rows.append(entry)
 exhausted=all(row.get('resume_source_validation',{}).get('valid') and row.get('cached_verification_binding',{}).get('valid') and row.get('verified_summary',{}).get('task_status')=='SHARD_EXHAUSTED_WITH_CERTIFICATES' for row in rows)
 status='VERIFIED_YES_WITNESS' if witnesses else 'ALL_SIX_REPORTED_CERTIFIED_REQUIRES_FINAL_GLOBAL_AUDIT' if exhausted else '未完成任務'
 summary={'problem':'MOLS10-3','task_status':status,'exact':rows,'construction':[],'construction_status':'NOT_RUN_IN_E078','source_run_id':45301881745,'witnesses':witnesses,'global_nonexistence_claim':False,
   'manifest_sha256':file_sha256(manifest_path),
   'verification_boundary':'The collector checks manifest/queue identity and cached replay bindings, but does not replay proofs. Global UNSAT still requires verify_family.py on all complete state archives.',
   'coverage':'Six simultaneous-even canonical cycle shards; 31 centralizer first-pair representatives. Missing and unresolved leaves remain explicit.',
   'resume':'Download the corresponding exact-N artifact and resume its saved state. Solver learned clauses are not retained. E078 does not run construction.',
   'imported_certificates_expected':10,'source_manifest_sha256':file_sha256(resume_manifest_path)}
 (target/'summary.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
 # Preserve small checkpoint metadata and concrete candidates on the results branch.
 # Complete CNFs and proofs remain in the per-job artifacts; none is silently dropped
 # from a supposedly replayable certificate directory.
 for folder in source.iterdir() if source.is_dir() else []:
  if not folder.is_dir():continue
  dest=target/'checkpoints'/folder.name
  for path in folder.rglob('*'):
   if path.is_file() and path.suffix in {'.json','.jsonl','.txt','.log'} and path.stat().st_size<4*1024*1024:
    to=dest/path.relative_to(folder);to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(path,to)
 shutil.copy2(resume_manifest_path,target/'resume_manifest.json')
 shutil.copy2(manifest_path,target/'coverage.json')
 print(json.dumps(summary,ensure_ascii=False))
if __name__=='__main__':main()
