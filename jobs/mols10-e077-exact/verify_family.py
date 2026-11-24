#!/usr/bin/env python3
"""Combine the exact required shard family only after replaying certificates.

--states is a JSON object mapping shard IDs to local state-directory paths.
Missing or unresolved shards remain explicit. No elapsed-time estimates.
"""
import argparse,hashlib,json,pathlib
from types import SimpleNamespace
from encode import VERSION,encode,partitions
from queue_search import atomic_json,load_state,verify_state

def main():
    p=argparse.ArgumentParser();p.add_argument('--manifest',required=True);p.add_argument('--states',required=True)
    p.add_argument('--out',required=True);p.add_argument('--lrat-check',default='lrat-check')
    p.add_argument('--check-seconds',type=float,default=900);a=p.parse_args()
    manifest=json.loads(pathlib.Path(a.manifest).read_text());states=json.loads(pathlib.Path(a.states).read_text())
    assert manifest['version']==VERSION
    n=manifest['n'];m=manifest['squares'];even=manifest['even_row_normalization']
    if even:assert n>2**m
    expected={i:parts for i,parts in enumerate(partitions(n)) if not even or (n-len(parts))%2==0}
    listed={row['shard']:row for row in manifest['required_shards']}
    assert set(listed)==set(expected) and len(listed)==len(manifest['required_shards'])
    for i,parts in expected.items():
        f,meta=encode(n,m,parts,even_second_rows=even)
        assert listed[i]['parts']==list(parts)
        assert listed[i]['cnf_sha256']==hashlib.sha256(f.dimacs().encode()).hexdigest()
    assert all(str(int(i))==i and int(i) in expected for i in states)
    rows=[];sat=[]
    for i in sorted(expected):
        if str(i) not in states:
            rows.append({'shard':i,'status':'MISSING_STATE'});continue
        d,q,meta=load_state(states[str(i)])
        assert q['shard']==i and q['n']==n and q['squares']==m and q['even_row_normalization']==even
        assert q['base_cnf_sha256']==listed[i]['cnf_sha256']
        result=verify_state(SimpleNamespace(state=d,lrat_check=a.lrat_check,check_seconds=a.check_seconds))
        rows.append({'shard':i,'status':result['task_status'],'verification':result})
        if result['task_status']=='VERIFIED_SAT_WITNESS':sat.append(i)
    if sat:status='VERIFIED_ORIGINAL_SAT_WITNESS'
    elif all(row['status']=='SHARD_EXHAUSTED_WITH_CERTIFICATES' for row in rows):
        status='ALL_REQUIRED_SHARDS_UNSAT_VERIFIED'
    else:status='未完成任務'
    result={'task_status':status,'n':n,'squares':m,'normalization':manifest['normalization'],
            'required_shards':sorted(expected),'shards':rows,
            'trust_boundary':'mathematical normalization and CNF equivalence are proved in prose; executable encoding, LRAT checker, and SAT witness verifier are not formalized in Lean here'}
    atomic_json(a.out,result);print(json.dumps(result,ensure_ascii=False))

if __name__=='__main__':main()
