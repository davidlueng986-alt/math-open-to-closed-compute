#!/usr/bin/env python3
"""Targeted E078 regression gate: actual proof formats, safe splitting and disk deferral.

No order-ten SAT search is performed. Original encoding/coverage hashes are
checked, and every accepted negative answer still passes DRAT and LRAT.
"""
import argparse,copy,hashlib,itertools,json,pathlib,random,shutil,subprocess,sys,time
from types import SimpleNamespace as NS
from encode import encode,sha256_file
from proof import detect_drat_format,verify_unsat
from queue_search import (UnitPropagator,atomic_json,choose_split,init_state,launch_solver,
                          load_state,proof_budget,resume_unverified,run_state,save_state,split_node,verify_state)

HERE=pathlib.Path(__file__).resolve().parent

def pigeonhole(pigeons=5,holes=4):
    variable=lambda p,h:p*holes+h+1
    clauses=[[variable(p,h) for h in range(holes)] for p in range(pigeons)]
    clauses += [[-variable(p,h),-variable(q,h)] for h in range(holes)
                for p,q in itertools.combinations(range(pigeons),2)]
    return f'p cnf {pigeons*holes} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)

def literal_truth(lit,assignment):
    return assignment[abs(lit)-1]==(lit>0)

def check_bcp_and_selection():
    rng=random.Random(780078);checked=0
    for _ in range(60):
        clauses=[[rng.choice((-1,1))*rng.randint(1,5) for _ in range(rng.randint(0,4))]
                 for _ in range(rng.randint(1,12))]
        assumptions=[rng.choice((-1,1))*rng.randint(1,5) for _ in range(rng.randint(0,2))]
        assigned=UnitPropagator(clauses).propagate(assumptions)
        models=[a for a in itertools.product((False,True),repeat=5)
                if all(literal_truth(x,a) for x in assumptions)
                and all(any(literal_truth(x,a) for x in c) for c in clauses)]
        if assigned is None:assert not models
        else:assert all(all(a[v-1]==t for v,t in assigned.items()) for a in models)
        checked+=1
    # x is forced by a failed literal, although there is no unit clause.
    # y is genuinely free and is the desired split. Neither branch is dropped.
    clauses=[[1,2],[1,-2]];original=copy.deepcopy(clauses);cube=[]
    mapping={'nvars':2,'variables':[{'id':i,'square':'L0','r':1,'c':0,'value':i} for i in (1,2)]}
    info={};chosen=choose_split(mapping,cube,clauses,64,info)
    assert chosen==2 and info['rejected_one_sided_variables']==[1]
    assert clauses==original and cube==[]
    q={'nodes':{'root':{'status':'PENDING','cube':[]}}}
    split_node(q,'root',chosen)
    assert q['nodes']['root0']['cube']==[-2] and q['nodes']['root1']['cube']==[2]
    assert all(q['nodes'][key]['status']=='PENDING' for key in ('root0','root1'))
    return {'exhaustive_small_formula_checks':checked,'failed_literal_example':info,
            'both_children_saved_without_closure':True}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',required=True,type=pathlib.Path)
    parser.add_argument('--kissat',default='kissat')
    parser.add_argument('--drat-trim',default='drat-trim')
    parser.add_argument('--lrat-check',default='lrat-check')
    args=parser.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    report={'status':'RUNNING','checks':{},'trust_boundary':'BCP chooses variables only; proof checkers still gate every negative leaf.'}
    report['checks']['bcp']=check_bcp_and_selection()
    coverage=json.loads((HERE/'coverage.json').read_text())
    comparisons=[];old_leaf_checks=[]
    # The ten fast, certified E077 leaves. Only four conflict under BCP;
    # the remaining six require stronger reasoning, so do not promise that
    # this selection heuristic eliminates every easy negative branch.
    old_leaves={1:[[-522,523],[-522,-523,524],[-522,-523,-524,525],[-522,-523,-524,-525,-526]],
                2:[[-522,523],[-522,-523,-524]],6:[[-522]],8:[[-522,-523]],
                9:[[-522,-523,-524]],10:[[-522,-523,-524,-525]]}
    for row in coverage['required_shards']:
        formula,mapping=encode(10,3,row['parts'],even_second_rows=True)
        assert hashlib.sha256(formula.dimacs().encode()).hexdigest()==row['cnf_sha256']
        info={};chosen=choose_split(mapping,[],formula.clauses,64,info)
        assert chosen is not None and info.get('selected_both_polarities_bcp_consistent')
        engine=UnitPropagator(formula.clauses)
        assert engine.propagate([-chosen]) is not None and engine.propagate([chosen]) is not None
        comparisons.append({'shard':row['shard'],'base_cnf_hash_unchanged':True,'selection':info})
        for old_cube in old_leaves[row['shard']]:
            info={};chosen=choose_split(mapping,old_cube[:-1],formula.clauses,64,info)
            conflict=engine.propagate(old_cube) is None
            if conflict:assert abs(old_cube[-1]) in info['rejected_one_sided_variables']
            assert chosen is not None and info.get('selected_both_polarities_bcp_consistent')
            old_leaf_checks.append({'shard':row['shard'],'old_cube':old_cube,
                                    'bcp_conflict':conflict,'selection':info})
    report['checks']['six_unchanged_encodings_and_splits']=comparisons
    assert sum(row['bcp_conflict'] for row in old_leaf_checks)==4
    report['checks']['recorded_e077_trivial_leaf_selections']=old_leaf_checks
    proof_cases=[]
    for mode in ('kissat_binary','kissat_ascii','pysat_ascii'):
        folder=args.out/mode;folder.mkdir(exist_ok=True)
        cnf=folder/'instance.cnf';proof=folder/'proof.drat';log=folder/'solver.log'
        cnf.write_text(pigeonhole())
        if mode=='kissat_ascii':
            command=[args.kissat,'--no-binary','--time=30',str(cnf),str(proof)]
            with log.open('wb') as output:
                solved=subprocess.run(command,stdout=output,stderr=subprocess.STDOUT,timeout=40)
            assert solved.returncode==20
            launch={'command':command,'returncode':solved.returncode}
        else:
            backend=args.kissat if mode=='kissat_binary' else 'pysat:cadical195'
            launch=launch_solver(backend,cnf,proof,log,30,8*1024**2)
            assert launch['returncode']==20,launch
        expected='binary_drat' if mode=='kissat_binary' else 'ascii_drat'
        assert detect_drat_format(proof)==expected
        checked=verify_unsat(cnf,proof,args.drat_trim,args.lrat_check,30)
        assert checked['status']=='UNSAT_VERIFIED',checked
        proof_cases.append({'case':mode,'launch':launch,'proof_bytes':proof.stat().st_size,'proof_check':checked})
    report['checks']['actual_solver_proof_formats_and_replay']=proof_cases
    # A valid, completed binary proof must survive verification deferral intact.
    src=args.out/'kissat_binary';deferred=args.out/'deferred';deferred.mkdir(exist_ok=True)
    for name in ('instance.cnf','proof.drat'):shutil.copy2(src/name,deferred/name)
    before=sha256_file(deferred/'proof.drat')
    reserve=shutil.disk_usage(deferred).free+1024**2
    checked=verify_unsat(deferred/'instance.cnf',deferred/'proof.drat',args.drat_trim,args.lrat_check,30,disk_reserve_bytes=reserve)
    assert checked['status']=='UNSAT_AWAITING_VERIFICATION'
    assert checked['verification_deferred']=='DISK_RESERVE_LIMIT'
    assert sha256_file(deferred/'proof.drat')==before
    replay=verify_unsat(deferred/'instance.cnf',deferred/'proof.drat',args.drat_trim,args.lrat_check,30)
    assert replay['status']=='UNSAT_VERIFIED'
    slow_checker=args.out/'slow-lrat-check.py'
    slow_checker.write_text(f'#!{sys.executable}\nimport time\ntime.sleep(30)\n')
    slow_checker.chmod(0o755)
    timed=verify_unsat(deferred/'instance.cnf',deferred/'proof.drat',args.drat_trim,str(slow_checker),1)
    assert timed['status']=='UNSAT_AWAITING_VERIFICATION' and timed['verification_deferred']=='CHECK_TIME_LIMIT'
    assert sha256_file(deferred/'proof.drat')==before
    budget=proof_budget(deferred,16*1024**3,reserve,3.0)
    assert budget['effective_max_proof_bytes']==0
    skipped=launch_solver(args.kissat,deferred/'instance.cnf',deferred/'unstarted.drat',deferred/'unstarted.log',30,16*1024**3,reserve,3.0)
    assert skipped['stop_reason']=='DISK_RESERVE_LIMIT' and not skipped['launched']
    report['checks']['disk_deferral_preserves_completed_proof']={'deferred_check':checked,'resumed_status':replay['status'],'budget':budget,'launch_skipped':skipped}
    report['checks']['time_deferral_preserves_completed_proof']=timed
    queues=[]
    for shard,expected in ((0,'VERIFIED_SAT_WITNESS'),(1,'SHARD_EXHAUSTED_WITH_CERTIFICATES')):
        state=args.out/f'n4_shard{shard}'
        init_state(NS(state=state,n=4,squares=3,shard=shard,amo='pairwise',even_row_normalization=False))
        run_state(NS(state=state,seconds=60,slice_seconds=30,solver=args.kissat,max_proof_bytes=8*1024**2,
                     disk_reserve_bytes=0,proof_expansion_factor=3.0,split_lookahead=64,split_unknown=True,
                     drat_trim=args.drat_trim,lrat_check=args.lrat_check,check_seconds=5))
        verified=verify_state(NS(state=state,lrat_check=args.lrat_check,check_seconds=10))
        assert verified['task_status']==expected;queues.append(verified)
        if shard==1:
            d,q,_=load_state(state);node=q['nodes']['root']
            result_path=d/node['evidence'];result=json.loads(result_path.read_text());folder=result_path.parent
            originals={name:sha256_file(folder/name) for name in ('instance.cnf','proof.drat','proof.lrat')}
            node['status']='UNSAT_AWAITING_VERIFICATION';save_state(d,q)
            # This intentionally invalid converter path proves resume uses
            # the existing LRAT, rather than silently re-converting DRAT.
            restored=resume_unverified(d,q,'root',NS(drat_trim='/must-not-be-called',lrat_check=args.lrat_check,check_seconds=10))
            assert restored=='UNSAT_VERIFIED'
            assert originals=={name:sha256_file(folder/name) for name in originals}
            report['checks']['existing_lrat_resume_preserves_certificate_bytes']={'status':restored,'sha256':originals}
    report['checks']['actual_kissat_sat_unsat_queues']=queues
    report['upstream_format_audit']={'kissat_commit':'8af8e56f174b778aef3aa45af9f739b2a5f492c2',
        'source':'https://github.com/arminbiere/kissat/blob/8af8e56f174b778aef3aa45af9f739b2a5f492c2/src/application.c',
        'regular_file_default':'binary_drat','E077_already_binary':True,'format_change_speedup_claim':False}
    report['status']='PASS';atomic_json(args.out/'summary.json',report)
    print(json.dumps({'status':'PASS','summary':str(args.out/'summary.json')},ensure_ascii=False))

if __name__=='__main__':main()
