#!/usr/bin/env python3
"""Kaggle CPU notebook launcher: four covered subcases, bounded worker pool."""
import argparse,concurrent.futures,gzip,hashlib,json,math,os,subprocess,sys,time,urllib.request
from pathlib import Path
import d9
p=argparse.ArgumentParser();p.add_argument('--c',type=int,required=True);p.add_argument('--out',required=True);p.add_argument('--total-solve-seconds',type=int,default=12600);a=p.parse_args()
out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
HERE=Path(__file__).resolve().parent
def catalog():
    # Published complete census; exactly four 85-edge cases.
    url='https://users.cecs.anu.edu.au/~bdm/data/r38_27.g6.gz'
    f=out/'r38_27.g6.gz'
    with urllib.request.urlopen(url,timeout=60) as r,open(f,'wb') as w:
        while True:
            b=r.read(1<<20)
            if not b:break
            w.write(b)
    n=0;selected=[]
    with gzip.open(f,'rt',encoding='ascii') as fp:
        for s in fp:
            s=s.strip().removeprefix('>>graph6<<')
            if not s:continue
            assert len(s)==60 and ord(s[0])-63==27
            n+=1
            if sum((ord(x)-63).bit_count() for x in s[1:])==85:
                g=d9.decode(s)
                assert sum(v.bit_count() for v in g)==170
                assert all(not(g[i]&g[j]) for i in range(27) for j in d9.bits(g[i]))
                assert not list(d9.independent(g,range(27),8,1))
                selected.append(s)
    assert n==477142 and len(selected)==4 and len(set(selected))==4
    digest=d9.sha(f);f.unlink()
    (out/'catalog.json').write_text(json.dumps(dict(url=url,total=n,sha256=digest,cores=selected),indent=2)+'\n')
    return selected
d9.selftest()
cores=None
if a.c==7:
    try:cores=catalog()
    except Exception as ex:
        print('Catalog import failed; fallback to complete unrestricted c7 T-degree partition:',repr(ex),flush=True)
        (out/'catalog_error.txt').write_text(repr(ex))
specs=d9.shards(a.c,cores)
workers=min(4,len(specs),len(os.sched_getaffinity(0)) if hasattr(os,'sched_getaffinity') else (os.cpu_count() or 1))
# Limit total wall time even on notebooks with fewer CPU cores.
budget=a.total_solve_seconds//math.ceil(len(specs)/workers)
plan=dict(c=a.c,workers=workers,seconds_per_worker=budget,proof_seconds=600,specs=specs,catalog_import=cores is not None)
d9.save(out/'plan.json',plan);print(json.dumps(plan),flush=True)
def one(i,spec):
    dest=out/f'shard-{i}';dest.mkdir(exist_ok=True)
    with open(dest/'run.log','w') as log:
        r=subprocess.run([sys.executable,'-u',str(HERE/'d9.py'),'--c',str(a.c),'--spec',json.dumps(spec),'--out',str(dest),'--seconds',str(budget),'--proof-seconds','600'],stdout=log,stderr=subprocess.STDOUT)
    if (dest/'witness.txt').exists():
        with open(dest/'witness-check.json','w') as log:
            q=subprocess.run([sys.executable,str(HERE.parent/'ramsey-r310-wave1'/'verify.py'),str(dest/'witness.txt')],stdout=log,stderr=subprocess.STDOUT)
        assert q.returncode==0 and json.loads((dest/'witness-check.json').read_text())['closure_witness']
        ret=json.loads((dest/'result.json').read_text());ret['status']='VERIFIED_WITNESS';d9.save(dest/'result.json',ret)
    return r.returncode
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
    fs=[ex.submit(one,i,s) for i,s in enumerate(specs)]
    while not all(f.done() for f in fs):
        summary=[]
        for i in range(len(specs)):
            try:summary.append(json.loads((out/f'shard-{i}'/'result.json').read_text()))
            except Exception:summary.append(dict(status='NOT_STARTED_OR_BUILDING'))
        print(json.dumps([dict(status=s.get('status'),models=s.get('models',0),cuts=s.get('cuts',0)) for s in summary]),flush=True)
        time.sleep(30)
    exitcodes=[]
    for f in fs:
        try:exitcodes.append(f.result())
        except Exception as e:exitcodes.append(repr(e))
results=[]
for i in range(len(specs)):
    try:results.append(json.loads((out/f'shard-{i}'/'result.json').read_text()))
    except Exception:results.append(dict(status='OPEN_NO_RESULT',spec=specs[i]))
status='OPEN'
if any(x.get('status')=='VERIFIED_WITNESS' for x in results):status='VERIFIED_WITNESS'
elif all(x.get('status')=='CERTIFIED_UNSAT' and x.get('certificate')=='VERIFIED_UNSAT' for x in results):status='CANDIDATE_CLOSED_C'+str(a.c)+'_PENDING_ENCODING_AUDIT'
d9.save(out/'summary.json',dict(c=a.c,status=status,exitcodes=exitcodes,plan=plan,results=results))
print((out/'summary.json').read_text(),flush=True)
