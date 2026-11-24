#!/usr/bin/env python3
"""Certificate-critical lifecycle checks; does not probe order-10 shards."""
import argparse,copy,json,pathlib,sys
from types import SimpleNamespace as NS
from queue_search import (atomic_json,choose_split,init_state,load_state,read_dimacs,
                          run_state,save_state,split_node,verify_state)

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',required=True)
    p.add_argument('--drat-trim',required=True);p.add_argument('--lrat-check',required=True)
    a=p.parse_args();out=pathlib.Path(a.out);out.mkdir(parents=True,exist_ok=True)
    records=[]
    for name,shard,expected in [('sat',0,'VERIFIED_SAT_WITNESS'),('split_unsat',1,'SHARD_EXHAUSTED_WITH_CERTIFICATES')]:
        state=out/name
        init_state(NS(state=state,n=4,squares=3,shard=shard,amo='pairwise',even_row_normalization=False))
        d,q,m=load_state(state)
        if name=='split_unsat':
            # This lifecycle test deliberately creates two children of an
            # already UNSAT control. Bypass failed-literal selection here;
            # test_e078.py separately checks the production lookahead.
            _,clauses=read_dimacs(d/'base.cnf');lit=choose_split(m,[],clauses,lookahead_candidates=0);assert lit is not None
            split_node(q,'root',lit)
            # Simulate a persisted running leaf after process interruption.
            q['nodes']['root0']['status']='RUNNING';save_state(d,q)
        run_state(NS(state=state,seconds=90,slice_seconds=30,solver='pysat:cadical195',
                     max_proof_bytes=10000000,split_unknown=True,drat_trim=a.drat_trim,
                     lrat_check=a.lrat_check,check_seconds=5))
        args=NS(state=state,lrat_check=a.lrat_check,check_seconds=5)
        verified=verify_state(args);assert verified['task_status']==expected;records.append(verified)
        if name=='split_unsat':
            d,q,m=load_state(state);original=copy.deepcopy(q)
            q['nodes']['root1']['cube']=q['nodes']['root0']['cube']
            atomic_json(d/'queue.json',q)
            try:verify_state(args)
            except AssertionError:records.append({'duplicate_child_tamper_rejected':True})
            else:raise AssertionError('Coverage checker accepted two identical child branches')
            atomic_json(d/'queue.json',original)
            q=original;node=next(v for v in q['nodes'].values() if v['status']=='UNSAT_VERIFIED')
            result_path=d/node['evidence'];result=json.loads(result_path.read_text())
            proof_path=result_path.parent/result['proof_check']['lrat'];original_proof=proof_path.read_bytes()
            proof_path.write_bytes(original_proof+b'\n')
            try:verify_state(args)
            except AssertionError:records.append({'proof_digest_tamper_rejected':True})
            else:raise AssertionError('Certificate digest mutation was accepted')
            proof_path.write_bytes(original_proof)
            verify_state(args)
    atomic_json(out/'summary.json',records)

if __name__=='__main__':main()
