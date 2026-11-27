#!/usr/bin/env python3
"""Persistent proof tree. Each split is x OR not x on an original edge variable.
Only universally valid I10 clauses are transported across independently solved cubes."""
import argparse,hashlib,importlib.util,itertools,json,os,random,shutil,subprocess,sys,time,gzip
from pathlib import Path
HERE=Path(__file__).resolve().parent
from plan import canon,sha,save,make
spec=importlib.util.spec_from_file_location('ramsey_v5',HERE.parent/'ramsey-r310-d678-v5'/'solve.py')
v5=importlib.util.module_from_spec(spec);spec.loader.exec_module(v5)
from pysat.solvers import Solver
from pysat.formula import CNF
e=v5.e;d9=v5.d9;N=40
def digest(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def cnf_digest(nv,clauses,cube=()):
 h=hashlib.sha256();h.update(f'p cnf {nv} {len(clauses)+len(cube)}\n'.encode())
 for cl in itertools.chain(clauses,([v] for v in cube)):
  h.update((' '.join(map(str,cl))+' 0\n').encode())
 return h.hexdigest()
def valid_cut(s):
 assert len(s)==10 and s==sorted(set(s)) and min(s)>=0 and max(s)<40
 return d9.cut(s)
def project(z,s):
 c=valid_cut(s)
 if any(z.val(x) is True for x in c):return None
 return tuple(x for x in c if z.val(x) is None)
def validate_tree(st):
 ns=st['nodes'];assert 'r' in ns and ns['r']['cube']==[]
 stack=['r'];seen=set()
 while stack:
  k=stack.pop();assert k not in seen;seen.add(k);n=ns[k];c=n['cube']
  assert len({abs(x) for x in c})==len(c) and all(1<=abs(x)<=780 for x in c)
  if n['status']=='SPLIT':
   x=n['split_var'];assert 1<=x<=780 and x not in map(abs,c)
   assert ns[k+'0']['cube']==c+[-x] and ns[k+'1']['cube']==c+[x]
   stack.extend([k+'0',k+'1'])
  else:assert n['status'] in ('OPEN','CERTIFIED_UNSAT','VERIFIED_WITNESS','UNSAT_UNCERTIFIED')
 assert seen==set(ns)
def preflight_resume(path,required=False):
 """Read required restore metadata before creating or overwriting output."""
 resume=Path(path) if path else None
 restored=None
 if resume and (resume/'checkpoint.json').is_file():
  restored=json.loads((resume/'checkpoint.json').read_text())
  if restored.get('status')=='VERIFIED_WITNESS' or any(
      n.get('status')=='VERIFIED_WITNESS' for n in restored.get('nodes',{}).values()):
   raise RuntimeError('Resume contains a verified witness; preserve and independently verify its witness artifact before any continuation')
 elif required:
  raise RuntimeError('--require-resume needs an existing checkpoint.json')
 elif resume and resume.exists() and any(resume.iterdir()):
  raise RuntimeError('Nonempty resume directory has no checkpoint')
 return resume,restored
def solve(a):
 resume,restored=preflight_resume(a.resume,a.require_resume)
 out=Path(a.out)
 if resume is not None and out.resolve()==resume.resolve():
  raise RuntimeError('Resume source and output must be different directories')
 out.mkdir(parents=True,exist_ok=True)
 plan=json.loads(Path(a.plan).read_text())
 # Recompute exact source partition and verify supplied task identity.
 task=next(t for t in plan['tasks'] if t['id']==a.task)
 assert task['key']==sha({k:v for k,v in task.items() if k!='key'})
 # The whole plan's explicit coverage is checked in its generator; verify
 # the selected profiles again directly against the exact v6 certificate.
 from profile import verified_partition
 from branch import supports
 kept=set(verified_partition(a.cert))
 d,q,m=task['d'],task['q'],task['m']
 ns=[tuple(n) for n in task['profiles']]
 assert ns and len(ns)==len(set(ns))
 assert all((n,m) in kept and supports(n,m,d,q,True) for n in ns)
 v5.support=lambda dd,qq:[(n,m) for n in ns] if (dd,qq)==(d,q) else []
 band=dict(lo=m,hi=m)
 z,ss=v5.formula(d,q,band)
 assert {n for n,mm in ss}==set(ns)
 X,Y,T,A,B=v5.groups(d,q);H0=Y+T;H1=X+T
 z.brange([e(i,j) for i in X for j in Y],task['tlo'],task['thi'])
 f=z.f
 base=list(f.clauses);base_nv=f.nv;base_sha=cnf_digest(base_nv,base)
 (out/'task.json').write_text(json.dumps(task,indent=2)+'\n')
 st=dict(schema=1,task=task,base_sha256=base_sha,nodes={'r':dict(cube=[],status='OPEN',attempts=0)},models=0,cuts=0)
 prior_rows=[]
 if restored is not None:
  st=restored
  assert st['task']==task and st['base_sha256']==base_sha
  validate_tree(st)
  for line in (resume/'cuts.jsonl').read_text().splitlines():prior_rows.append(json.loads(line))
  # A checkpoint may have valid extra cuts flushed just before its last
  # atomic manifest update. They are still valid; never drop them.
  assert st['cuts']<=len(prior_rows)
  if (resume/'proofs').exists():shutil.copytree(resume/'proofs',out/'proofs',dirs_exist_ok=True)
 seen=set();rows=[];cutclauses=[]
 def append(s,fp,sol=None):
  s=list(s);c=project(z,s)
  if c is None or c in seen:return False
  seen.add(c);rows.append(s);cutclauses.append(list(c));f.append(list(c));fp.write(json.dumps(s)+'\n')
  if sol is not None:sol.add_clause(list(c))
  return True
 def checkpoint():
  st['cuts']=len(rows);validate_tree(st)
  terminals=[n['status'] for n in st['nodes'].values() if n['status']!='SPLIT']
  st['status']='VERIFIED_WITNESS' if 'VERIFIED_WITNESS' in terminals else ('ALL_CUBES_CERTIFIED_UNSAT_PENDING_ENCODING_AUDIT' if all(t=='CERTIFIED_UNSAT' for t in terminals) else 'OPEN')
  st['terminal_counts']={t:terminals.count(t) for t in sorted(set(terminals))}
  save(out/'checkpoint.json',st)
  print(json.dumps(dict(task=task['id'],status=st['status'],terminals=st['terminal_counts'],cuts=st['cuts'],models=st['models'])),flush=True)
 def replay_saved(k,n):
  # Rebuild expected CNF identity from exact base, validated original cuts,
  # and the precise cube. Check the stored proof hash; replay DRAT again.
  pp=out/'proofs'/k;meta=n['proof'];cnt=meta['cut_count']
  assert 0<=cnt<=len(cutclauses)
  # proof writer uses PySAT DIMACS; reconstruct via exactly same CNF writer.
  test=CNF(from_clauses=base+cutclauses[:cnt]+[[x] for x in n['cube']]);test.nv=max(test.nv,base_nv)
  tmp=pp/'replay.cnf';test.to_file(str(tmp));assert digest(tmp)==meta['cnf_sha256']
  raw=pp/'replay.drat'
  with gzip.open(pp/'leaf.drat.gz','rb') as fi,open(raw,'wb') as fo:shutil.copyfileobj(fi,fo)
  assert digest(raw)==meta['proof_sha256']
  try:
   with open(pp/'resume-check.log','w') as fo:
    rr=subprocess.run(['drat-trim',str(tmp),str(raw)],stdout=fo,stderr=subprocess.STDOUT,timeout=a.proof_seconds)
   assert rr.returncode==0 and 's VERIFIED' in (pp/'resume-check.log').read_text(errors='replace')
  finally:tmp.unlink(missing_ok=True);raw.unlink(missing_ok=True)
 start=time.monotonic();rng=random.Random(int(task['key'][:12],16)+len(prior_rows))
 with open(out/'cuts.jsonl','w',buffering=1) as fp:
  for s in prior_rows:assert append(s,fp), 'Prior cut stream is not exact unique prefix'
  # Verify all earlier terminal proofs before counting them as closed.
  for k,n in st['nodes'].items():
   if n['status']=='CERTIFIED_UNSAT':
    try:replay_saved(k,n)
    except (OSError,AssertionError,subprocess.TimeoutExpired) as ex:
     n['status']='UNSAT_UNCERTIFIED';n['replay_error']=str(ex)
   elif n['status']=='VERIFIED_WITNESS':
    # On resume don't claim a witness without its original exact replay.
    n['status']='OPEN'
  # Old artifacts use the same vertex labels or another labeling; the full
  # I10 clause is universal in either case. Reproject against this skeleton.
  for path in a.reuse:
   if Path(path).is_file():
    with open(path) as fi:
     for l in fi:append(json.loads(l),fp)
  # Seed exact root-neighborhood cuts; avoid a huge unstructured static CNF.
  for ss in itertools.combinations(X+Y,10):append(sorted(ss),fp)
  for nb,H in ((A,H0),(B,H1)):
   for ss in itertools.combinations(H,10-len(nb)):append(sorted(tuple(nb)+ss),fp)
  checkpoint()
  candidates=[e(i,j) for C,D in ((X,Y),(X,T),(Y,T),(T,T)) for i in C for j in D if i!=j and z.val(e(i,j)) is None]
  candidates=sorted(set(candidates))
  with Solver(name='cadical195',bootstrap_with=f.clauses) as sol:
   def choose(cube):
    avail=[v for v in candidates if v not in set(map(abs,cube))]
    if not avail:return None
    # Deterministic pseudo-random portfolio; prioritize meaningful cross edges
    # when available and use balanced unit propagation to choose a split.
    xy=[e(i,j) for i in X for j in Y if e(i,j) in avail]
    sample=list(dict.fromkeys(xy[:12]+rng.sample(avail,min(12,len(avail)))))
    best=None
    for v in sample:
     p=sol.propagate(assumptions=cube+[v]);n=sol.propagate(assumptions=cube+[-v])
     # If one child is unit-inconsistent, still retain both for proof.
     a1=len(p[1]) if p[0] else 1000000;a2=len(n[1]) if n[0] else 1000000
     score=(min(a1,a2),max(a1,a2))
     if best is None or score>best[0]:best=(score,v)
    return best[1] if best else avail[0]
   attempted=set()
   while time.monotonic()-start<a.seconds and len(rows)<a.cut_cap:
    pending=[k for k,n in st['nodes'].items() if n['status'] in ('OPEN','UNSAT_UNCERTIFIED') and k not in attempted]
    if not pending or st['status']=='VERIFIED_WITNESS':break
    k=min(pending,key=lambda s:(len(s),s));n=st['nodes'][k];cube=n['cube'];n['attempts']+=1
    attempted.add(k)
    deadline=min(start+a.seconds,time.monotonic()+a.cube_seconds);unsat=False
    # Even if last attempt said UNSAT, require a real proof again.
    while time.monotonic()<deadline and len(rows)<a.cut_cap:
     sol.conf_budget(25000);r=sol.solve_limited(assumptions=cube)
     if r is None:continue
     if r is False:unsat=True;break
     g=d9.graph(sol.get_model());v5.verify_graph(g,d,q,band)
     assert tuple(sum(x.bit_count()==j for x in g) for j in (6,7,8,9)) in ns
     assert task['tlo']<=sum(g[i]>>j&1 for i in X for j in Y)<=task['thi']
     st['models']+=1;bad=set()
     for verts,k2,prefix,limit in ((H0,9,(0,),256),(H1,9,(1,),256),(range(N),10,(),512)):
      for ss in d9.independent(g,verts,k2,limit,rng):bad.add(tuple(sorted(prefix+ss)))
     if not bad:
      assert not list(d9.independent(g,range(N),10,1))
      wp=out/'witness.txt';wp.write_text(''.join(''.join(str(g[i]>>j&1) for j in range(N))+'\n' for i in range(N)))
      with open(out/'witness-check.json','w') as log:
       rr=subprocess.run([sys.executable,str(HERE.parent/'ramsey-r310-wave1'/'verify.py'),str(wp)],stdout=log,stderr=subprocess.STDOUT)
      assert rr.returncode==0 and json.loads((out/'witness-check.json').read_text())['closure_witness']
      n['status']='VERIFIED_WITNESS';checkpoint();return
     add=0
     for ss in sorted(bad):
      assert all(not(g[i]>>j&1) for i,j in d9.pairs if i in ss and j in ss)
      add+=append(list(ss),fp,sol)
     assert add
     if st['models']%5==0:checkpoint()
    if unsat:
     # Reserve actual time for proof generation AND replay. Do not pretend
     # incremental UNSAT is certified if the second solver exhausts time.
     rem=int(start+a.seconds-time.monotonic());budget=min(a.proof_seconds,max(0,(rem-10)//2))
     if budget>=15:
      dest=out/'proofs'/k;dest.mkdir(parents=True,exist_ok=True)
      f2=CNF(from_clauses=base+cutclauses+[[v] for v in cube]);f2.nv=max(f2.nv,base_nv)
      meta=v5.repair.proof(f2,dest,budget)
      meta['cut_count']=len(rows)
      if meta.get('certificate')=='VERIFIED_UNSAT':
       n['status']='CERTIFIED_UNSAT';n['proof']=meta
       # Keep exact CNF hash and compressed proof; base+cuts reconstruct CNF.
       (dest/'leaf.cnf').unlink(missing_ok=True)
       checkpoint();continue
      n['status']='UNSAT_UNCERTIFIED';n['proof_attempt']=meta
     else:n['status']='UNSAT_UNCERTIFIED'
    # Split a timeout (or unverified UNSAT) into both complementary cubes.
    if len(cube)<a.max_depth and time.monotonic()<start+a.seconds-5:
     var=choose(cube)
     if var is not None:
      n['status']='SPLIT';n['split_var']=var
      for b,lit in [('0',-var),('1',var)]:st['nodes'][k+b]=dict(cube=cube+[lit],status='OPEN',attempts=0)
    checkpoint()
 checkpoint()
if __name__=='__main__':
 p=argparse.ArgumentParser()
 p.add_argument('--plan',required=True);p.add_argument('--cert',required=True);p.add_argument('--task',required=True);p.add_argument('--out',default='out')
 p.add_argument('--reuse',action='append',default=[]);p.add_argument('--resume')
 p.add_argument('--require-resume',action='store_true',help='Fail before writing output unless an existing non-witness checkpoint is restored')
 p.add_argument('--seconds',type=int,default=3000);p.add_argument('--cube-seconds',type=int,default=180)
 p.add_argument('--proof-seconds',type=int,default=240);p.add_argument('--max-depth',type=int,default=7);p.add_argument('--cut-cap',type=int,default=800000)
 solve(p.parse_args())

