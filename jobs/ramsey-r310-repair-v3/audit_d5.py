#!/usr/bin/env python3
"""Second exact encoding for D5-Nq, independent of repair.py adder and lex.
Uses v2 standard cardinality networks, explicit lex prefix truth-table clauses,
and a second DRAT proof. A successful proof is for the same normalized case."""
import argparse,itertools,json,subprocess,sys,hashlib,gzip,shutil,resource
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ramsey-r310-dag-v2'))
from solve import base,e,cut
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
p=argparse.ArgumentParser();p.add_argument('--q',type=int,required=True);p.add_argument('--prior',required=True);p.add_argument('--out',required=True);p.add_argument('--seconds',type=int,default=1500);a=p.parse_args()
q=a.q;assert 5<=q<=9;out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
prior=Path(a.prior);meta=json.loads((prior/'result.json').read_text())
assert meta['branch']==f'D5-N{q}' and meta['status']=='CERTIFIED_UNSAT' and meta['certificate']=='VERIFIED_UNSAT'
def digest(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
assert digest(prior/'leaf.cnf')==meta['cnf_sha256']
with gzip.open(prior/'leaf.drat.gz','rb') as fi,open(out/'original.drat','wb') as fo:shutil.copyfileobj(fi,fo)
assert digest(out/'original.drat')==meta['proof_sha256']
with open(out/'original-check.log','w') as fo:
    c=subprocess.run(['drat-trim',str(prior/'leaf.cnf'),str(out/'original.drat')],stdout=fo,stderr=subprocess.STDOUT,timeout=300)
assert c.returncode==0 and 's VERIFIED' in (out/'original-check.log').read_text(errors='replace')
(out/'original.drat').unlink()
# Re-encode using the original v2 base (not v3's compact binary adders).
f=base(5,q,False);pool=IDPool(start_from=f.nv+1)
A=range(1,6);H=range(6,40)
for i in list(H)+(list(range(2,6)) if q==5 else []):
    f.extend(CardEnc.atleast([e(i,j) for j in range(40) if j!=i],bound=7,vpool=pool,encoding=EncType.totalizer).clauses)
# No auxiliary comparator variables: for every prefix assignment,
# prohibit 0 < 1 at the first unequal bit, directly on the original edges.
for i,j in zip(H,H[1:]):
    for row,u in enumerate(A):
        for b in itertools.product((0,1),repeat=row):
            c=[]
            for w,v in zip(A,b):
                c.extend([-e(w,i),-e(w,j)] if v else [e(w,i),e(w,j)])
            f.append(c+[e(u,i),-e(u,j)])
for i in H:f.append([e(1,i) if i-6<q-1 else -e(1,i)])
seen=set()
for line in (prior/'cuts.jsonl').read_text().splitlines():
    s=tuple(json.loads(line))
    assert len(s)==10 and s==tuple(sorted(set(s))) and min(s)>=0 and max(s)<40 and s not in seen
    seen.add(s);f.append(cut(s))
assert len(seen)==meta['cuts']
cnf=out/'alternate.cnf';f.to_file(str(cnf));proof=out/'alternate.drat'
result=dict(branch=f'D5-N{q}',status='ORIGINAL_DRAT_REPLAYED',original_cnf_sha256=meta['cnf_sha256'],original_proof_sha256=meta['proof_sha256'],cuts=len(seen),alternate_vars=f.nv,alternate_clauses=len(f.clauses))
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
def limit():resource.setrlimit(resource.RLIMIT_FSIZE,(768*1024**2,768*1024**2))
try:
    with open(out/'kissat.log','w') as fo:
        r=subprocess.run(['kissat',str(cnf),str(proof)],stdout=fo,stderr=subprocess.STDOUT,timeout=a.seconds,preexec_fn=limit)
    result['alternate_solver_exit']=r.returncode
    if r.returncode==20:
        with open(out/'alternate-check.log','w') as fo:
            c=subprocess.run(['drat-trim',str(cnf),str(proof)],stdout=fo,stderr=subprocess.STDOUT,timeout=300)
        if c.returncode==0 and 's VERIFIED' in (out/'alternate-check.log').read_text(errors='replace'):
            result.update(status='TWO_ENCODINGS_VERIFIED_UNSAT',alternate_cnf_sha256=digest(cnf),alternate_proof_sha256=digest(proof))
            with open(proof,'rb') as fi,gzip.open(out/'alternate.drat.gz','wb',compresslevel=1) as fo:shutil.copyfileobj(fi,fo)
    if result['status']!='TWO_ENCODINGS_VERIFIED_UNSAT':cnf.unlink(missing_ok=True)
except (OSError,subprocess.TimeoutExpired) as ex:result['replay_error']=str(ex);cnf.unlink(missing_ok=True)
finally:proof.unlink(missing_ok=True)
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
