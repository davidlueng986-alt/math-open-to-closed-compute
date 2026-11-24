#!/usr/bin/env python3
"""Resumable proof-producing cube queue for the normalized original problem.

One writer owns a state directory. Every split is an explicit exhaustive
Boolean dichotomy. Only independently checked LRAT or a directly checked
MOLS witness can finish a leaf. No elapsed-time completion percentages.
"""
from __future__ import annotations
import argparse,collections,hashlib,itertools,json,math,os,pathlib,re,shutil,signal,subprocess,sys,time
from encode import (VERSION,Formula,decode_model,encode,enforce_even_permutation,partitions,read_dimacs,sha256_file,
                    verify_model_cnf,verify_squares,write_instance)
from proof import detect_drat_format,replay_lrat,verify_unsat

HERE=pathlib.Path(__file__).resolve().parent
QUEUE_VERSION='mols-cube-queue-v1'

def atomic_json(path,data):
    path=pathlib.Path(path);tmp=path.with_name(path.name+'.tmp')
    with open(tmp,'w') as f:
        json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    tmp.replace(path)

def load_state(directory):
    d=pathlib.Path(directory);q=json.loads((d/'queue.json').read_text());m=json.loads((d/'mapping.json').read_text())
    assert q['version']==QUEUE_VERSION and m['version']==VERSION
    assert sha256_file(d/'base.cnf')==q['base_cnf_sha256']==m['cnf_sha256']
    assert sha256_file(d/'mapping.json')==q['mapping_sha256']
    return d,q,m

def save_state(d,q):
    q['updated_unix']=time.time();atomic_json(d/'queue.json',q)

def init_state(args):
    d=pathlib.Path(args.state)
    if (d/'queue.json').exists():
        _,q,m=load_state(d)
        assert (q['n'],q['squares'],q['shard'])==(args.n,args.squares,args.shard)
        assert m['amo']==args.amo and m['even_second_rows']==args.even_row_normalization
        return q
    choices=list(partitions(args.n));assert 0<=args.shard<len(choices)
    m=write_instance(d,args.n,args.squares,choices[args.shard],args.amo,even_second_rows=args.even_row_normalization)
    q={'version':QUEUE_VERSION,'n':args.n,'squares':args.squares,'shard':args.shard,
       'parts':list(choices[args.shard]),'base_cnf_sha256':m['cnf_sha256'],
       'even_row_normalization':args.even_row_normalization,
       'mapping_sha256':sha256_file(d/'mapping.json'),'root':'root','created_unix':time.time(),
       'nodes':{'root':{'cube':[],'parent':None,'status':'PENDING','attempts':[]}},
       'task_status':'未完成任務','coverage':'binary split tree; every child is parent plus a literal or its negation'}
    save_state(d,q);return q

def cube_cnf(base,output,cube):
    nvars,clauses=read_dimacs(base)
    assert all(isinstance(x,int) and 0<abs(x)<=nvars for x in cube)
    with open(output,'w') as f:
        f.write(f'p cnf {nvars} {len(clauses)+len(cube)}\n')
        for clause in clauses:f.write(' '.join(map(str,clause))+' 0\n')
        for x in cube:f.write(f'{x} 0\n')

def parse_solver_log(path):
    statuses=[];model=[];stats=[]
    for line in pathlib.Path(path).read_text(errors='replace').splitlines():
        if line.startswith('s '):statuses.append(line[2:].strip())
        elif line.startswith('v '):model.extend(x for x in map(int,line[2:].split()) if x)
        elif any(word in line for word in ('conflicts:','decisions:','restarts:','pysat_stats','process-time:','maximum-resident-set-size:')):
            stats.append(line)
    assert len(set(statuses))<=1
    return (statuses[-1] if statuses else 'UNKNOWN'),model,stats

def terminate(process):
    if process.poll() is not None:return
    try:os.killpg(process.pid,signal.SIGTERM)
    except ProcessLookupError:return
    try:process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:os.killpg(process.pid,signal.SIGKILL)
        except ProcessLookupError:pass
        process.wait()

def proof_budget(directory,max_proof_bytes,disk_reserve_bytes=0,proof_expansion_factor=1.0):
    """Bound proof output while reserving room for checking and saved state.

    The expansion factor is an engineering allowance, not a proved bound on
    LRAT expansion. A separate live disk guard also protects the reserve.
    """
    if max_proof_bytes<=0 or disk_reserve_bytes<0 or proof_expansion_factor<1:
        raise ValueError('invalid bounded-proof disk policy')
    free=shutil.disk_usage(directory).free
    effective=min(max_proof_bytes,max(0,int((free-disk_reserve_bytes)/proof_expansion_factor)))
    return {'requested_max_proof_bytes':max_proof_bytes,'effective_max_proof_bytes':effective,
            'disk_free_bytes_at_start':free,'disk_reserve_bytes':disk_reserve_bytes,
            'proof_expansion_factor':proof_expansion_factor}

def launch_solver(solver,cnf,proof,log,seconds,max_proof_bytes,
                  disk_reserve_bytes=0,proof_expansion_factor=1.0):
    budget=proof_budget(pathlib.Path(proof).parent,max_proof_bytes,disk_reserve_bytes,proof_expansion_factor)
    if solver.startswith('pysat:'):
        command=[sys.executable,str(HERE/'pysat_worker.py'),str(cnf),str(proof),'--solver',solver.split(':',1)[1]]
        expected_format='ascii_drat'
    else:
        # Kissat 4.0.4 already defaults to binary DRAT for regular files.
        # There is deliberately no unsupported '--binary' flag. '--no-binary'
        # and stdout are the upstream ASCII alternatives, neither used here.
        command=[solver,f'--time={max(1,int(seconds))}',str(cnf),str(proof)]
        expected_format='binary_drat'
    start=time.monotonic();reason=None
    with open(log,'wb') as output:
        if budget['effective_max_proof_bytes']<1024*1024:
            return {'command':command,'returncode':None,'seconds':0,'stop_reason':'DISK_RESERVE_LIMIT',
                    'launched':False,'proof_format_expected':expected_format,**budget}
        process=subprocess.Popen(command,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        try:
            while process.poll() is None:
                if time.monotonic()-start>seconds+10:
                    reason='WALL_LIMIT';terminate(process);break
                if proof.exists() and proof.stat().st_size>budget['effective_max_proof_bytes']:
                    reason='PROOF_SIZE_LIMIT';terminate(process);break
                if disk_reserve_bytes and shutil.disk_usage(pathlib.Path(proof).parent).free<disk_reserve_bytes:
                    reason='DISK_RESERVE_LIMIT';terminate(process);break
                time.sleep(0.25)
        except BaseException:
            terminate(process);raise
    return {'command':command,'returncode':process.returncode,'seconds':time.monotonic()-start,
            'stop_reason':reason,'launched':True,'proof_format_expected':expected_format,
            'proof_format_observed':detect_drat_format(proof),**budget}

class UnitPropagator:
    """Occurrence-indexed BCP used only to choose a branching variable.

    No result from this class closes a leaf, adds a clause to the base CNF,
    or changes a saved cube. Both children of every actual split are kept.
    """
    def __init__(self,clauses):
        self.lengths=[];self.xors=[];self.occurrences=collections.defaultdict(list);self.units=[]
        self.empty=False
        for clause in clauses:
            unique=list(dict.fromkeys(clause))
            if any(-lit in unique for lit in unique):continue
            if not unique:self.empty=True;continue
            index=len(self.lengths);self.lengths.append(len(unique));value=0
            for lit in unique:value^=lit;self.occurrences[lit].append(index)
            self.xors.append(value)
            if len(unique)==1:self.units.append(unique[0])

    def propagate(self,assumptions):
        if self.empty:return None
        lengths=self.lengths.copy();xors=self.xors.copy();satisfied=bytearray(len(lengths))
        assigned={};pending=collections.deque(self.units);pending.extend(assumptions)
        while pending:
            lit=pending.popleft();variable=abs(lit);truth=lit>0
            if variable in assigned:
                if assigned[variable]!=truth:return None
                continue
            assigned[variable]=truth
            for index in self.occurrences.get(lit,()):satisfied[index]=1
            for index in self.occurrences.get(-lit,()):
                if satisfied[index]:continue
                lengths[index]-=1;xors[index]^=-lit
                if lengths[index]==0:return None
                if lengths[index]==1:pending.append(xors[index])
        return assigned

def unit_closure(clauses,assumptions):
    return UnitPropagator(clauses).propagate(assumptions)

def choose_split(m,cube,base,lookahead_candidates=64,diagnostics=None):
    propagator=UnitPropagator(base);assigned=propagator.propagate(cube)
    info={'method':'BCP_AND_BOUNDED_FAILED_LITERAL_LOOKAHEAD','lookahead_limit':lookahead_candidates,
          'probed_variables':0,'rejected_one_sided_variables':[],'changes_base_or_cube':False}
    if diagnostics is not None:diagnostics.update(info);info=diagnostics
    if assigned is None:return None
    info['bcp_assigned_variables']=len(assigned)
    # Prefer original variables. First nontrivial second-row cells come before
    # later rows; channels are only a fallback. This changes efficiency only.
    candidates=sorted(m['variables'],key=lambda v:(not v['square'].startswith('L'),v['r'],v['c'],v['square'],v['value']))
    ordered=list(dict.fromkeys([v['id'] for v in candidates]+list(range(1,m['nvars']+1))))
    for variable in ordered:
        if variable in assigned:continue
        if info['probed_variables']>=lookahead_candidates:
            info.update(selected_variable=variable,lookahead_limit_reached=True)
            return variable
        info['probed_variables']+=1
        negative=propagator.propagate(list(cube)+[-variable])
        positive=propagator.propagate(list(cube)+[variable])
        if negative is None or positive is None:
            info['rejected_one_sided_variables'].append(variable)
            if negative is None and positive is None:
                info['both_polarities_conflict']=variable
                return None
            continue
        info.update(selected_variable=variable,selected_both_polarities_bcp_consistent=True)
        return variable
    return None

def split_node(q,key,lit):
    node=q['nodes'][key];assert node['status'] in ('PENDING','UNKNOWN','ERROR')
    assert abs(lit) not in {abs(x) for x in node['cube']}
    left=key+'0';right=key+'1';assert left not in q['nodes'] and right not in q['nodes']
    for name,sign in [(left,-lit),(right,lit)]:
        q['nodes'][name]={'cube':node['cube']+[sign],'parent':key,'status':'PENDING','attempts':[]}
    node.update(status='SPLIT',split_literal=lit,children=[left,right])

def queue_summary(q):
    leaves=[node for node in q['nodes'].values() if node['status']!='SPLIT']
    counts=dict(collections.Counter(node['status'] for node in leaves))
    if counts.get('SAT_VERIFIED'):task='VERIFIED_SAT_WITNESS'
    elif leaves and all(node['status']=='UNSAT_VERIFIED' for node in leaves):task='SHARD_EXHAUSTED_WITH_CERTIFICATES'
    else:task='未完成任務'
    q['task_status']=task
    return {'shard':q['shard'],'parts':q['parts'],'task_status':task,'nodes':len(q['nodes']),
            'leaves':len(leaves),'leaf_status_counts':counts,
            'coverage':'all unresolved leaves retained; no percentage estimate'}

def make_attempt(d,q,key):
    node=q['nodes'][key];number=len(node['attempts'])
    path=d/'attempts'/f'{key}_{number:04d}'
    while path.exists():
        number+=1;path=d/'attempts'/f'{key}_{number:04d}'
    path.mkdir(parents=True,exist_ok=False)
    relative=str(path.relative_to(d));node['attempts'].append(relative)
    cube_cnf(d/'base.cnf',path/'instance.cnf',node['cube'])
    atomic_json(path/'attempt.json',{'cube':node['cube'],'node':key,'cnf_sha256':sha256_file(path/'instance.cnf')})
    node['status']='RUNNING';save_state(d,q)
    return path

def finish_attempt(d,q,m,key,path,solver_result,args):
    node=q['nodes'][key]
    status,model,stats=parse_solver_log(path/'solver.log')
    result={'solver':solver_result,'solver_status':status,'solver_stats':stats,
            'cnf_sha256':sha256_file(path/'instance.cnf'),'cube':node['cube'],'status':'UNKNOWN'}
    if status=='SATISFIABLE' and solver_result['returncode']==10:
        verify_model_cnf(path/'instance.cnf',model)
        witness=decode_model(m,model)
        atomic_json(path/'witness.json',{'squares':witness,'model':model,'cnf_sha256':result['cnf_sha256']})
        result['status']='SAT_VERIFIED';result['witness']='witness.json'
        result['witness_sha256']=sha256_file(path/'witness.json')
        node['status']='SAT_VERIFIED';node['evidence']=str((path/'result.json').relative_to(d))
    elif status=='UNSATISFIABLE' and solver_result['returncode']==20 and (path/'proof.drat').exists():
        result['status']='UNSAT_AWAITING_VERIFICATION'
        atomic_json(path/'result.json',result)
        node['status']='UNSAT_AWAITING_VERIFICATION';node['evidence']=str((path/'result.json').relative_to(d));save_state(d,q)
        checked=verify_unsat(path/'instance.cnf',path/'proof.drat',args.drat_trim,args.lrat_check,args.check_seconds,
                             disk_reserve_bytes=getattr(args,'disk_reserve_bytes',0))
        result['proof_check']=checked;result['status']=checked['status'];node['status']=checked['status']
    else:
        node['status']='UNKNOWN'
    if result['status'] in ('UNKNOWN','SAT_VERIFIED') and (path/'proof.drat').exists():
        result['discarded_incomplete_drat']={'bytes':(path/'proof.drat').stat().st_size,
                                             'sha256':sha256_file(path/'proof.drat')}
        (path/'proof.drat').unlink()
    atomic_json(path/'result.json',result)
    if node['status']=='UNKNOWN' and args.split_unknown and solver_result.get('stop_reason')!='DISK_RESERVE_LIMIT':
        _,base=read_dimacs(d/'base.cnf')
        selection={}
        lit=choose_split(m,node['cube'],base,getattr(args,'split_lookahead',64),selection)
        result['split_selection']=selection
        if lit is not None:split_node(q,key,lit)
        atomic_json(path/'result.json',result)
    save_state(d,q)
    print(json.dumps({'node':key,'status':result['status'],'solver_seconds':solver_result.get('seconds'),
                      'queue':queue_summary(q)},ensure_ascii=False),flush=True)

def resume_unverified(d,q,key,args):
    node=q['nodes'][key];path=d/node['evidence'];result=json.loads(path.read_text());folder=path.parent
    assert result['cnf_sha256']==sha256_file(folder/'instance.cnf')
    previous=result.get('proof_check',{})
    if previous.get('lrat') and previous.get('lrat_sha256'):
        # A bounded final replay may defer an already generated certificate.
        # Replay it directly: conversion must never overwrite that LRAT.
        assert previous['cnf_sha256']==result['cnf_sha256']
        assert sha256_file(folder/previous['lrat'])==previous['lrat_sha256']
        checked=dict(previous)
        replay=replay_lrat(folder/'instance.cnf',folder/previous['lrat'],args.lrat_check,
                           folder/'resume-lrat.log',args.check_seconds)
        checked['resume_lrat_replay']=replay
        checked['status']=('UNSAT_VERIFIED' if replay['verified'] else
                           'UNSAT_AWAITING_VERIFICATION' if replay.get('stop_reason') else 'UNSAT_UNVERIFIED')
        if replay.get('stop_reason'):checked['verification_deferred']=replay['stop_reason']
        else:checked.pop('verification_deferred',None)
    else:
        checked=verify_unsat(folder/'instance.cnf',folder/'proof.drat',args.drat_trim,args.lrat_check,args.check_seconds,
                             disk_reserve_bytes=getattr(args,'disk_reserve_bytes',0))
    result['proof_check']=checked;result['status']=checked['status'];node['status']=checked['status']
    atomic_json(path,result);save_state(d,q)
    return checked['status']

def run_state(args):
    d,q,m=load_state(args.state);deadline=time.monotonic()+args.seconds
    # A hard process/job interruption never erases the cube. Any running leaf
    # is explicitly requeued; certificates are replayed by verify, not trusted.
    for key,node in q['nodes'].items():
        if node['status']=='RUNNING':
            node['status']='PENDING';node['recovered_after_interruption']=True
            if not node['attempts']:continue
            folder=d/node['attempts'][-1]
            # Recover a finished result after a hard interruption before the
            # queue update. A solver's UNSAT text alone never closes it.
            status='UNKNOWN';model=[]
            if (folder/'solver.log').exists():status,model,_=parse_solver_log(folder/'solver.log')
            if status=='UNSATISFIABLE' and (folder/'proof.drat').exists():
                result={'status':'UNSAT_AWAITING_VERIFICATION','cube':node['cube'],
                        'cnf_sha256':sha256_file(folder/'instance.cnf'),'recovered_after_interruption':True}
                atomic_json(folder/'result.json',result)
                node['status']='UNSAT_AWAITING_VERIFICATION';node['evidence']=str((folder/'result.json').relative_to(d))
            elif status=='SATISFIABLE':
                try:
                    verify_model_cnf(folder/'instance.cnf',model);witness=decode_model(m,model)
                except (AssertionError,ValueError):pass
                else:
                    atomic_json(folder/'witness.json',{'squares':witness,'model':model})
                    result={'status':'SAT_VERIFIED','cube':node['cube'],'cnf_sha256':sha256_file(folder/'instance.cnf'),
                            'witness':'witness.json','witness_sha256':sha256_file(folder/'witness.json'),
                            'recovered_after_interruption':True}
                    atomic_json(folder/'result.json',result)
                    node['status']='SAT_VERIFIED';node['evidence']=str((folder/'result.json').relative_to(d))
            if node['status']=='PENDING' and (folder/'proof.drat').exists():
                atomic_json(folder/'discarded_incomplete_proof.json',{'bytes':(folder/'proof.drat').stat().st_size,
                              'sha256':sha256_file(folder/'proof.drat'),'reason':'interrupted attempt; no completed certificate'})
                (folder/'proof.drat').unlink()
    save_state(d,q)
    deferred=set()
    while True:
        remaining=deadline-time.monotonic()
        if remaining<2*args.check_seconds+30:break
        unverified=[key for key,node in q['nodes'].items() if node['status'] in ('UNSAT_UNVERIFIED','UNSAT_AWAITING_VERIFICATION') and key not in deferred]
        if unverified:
            key=unverified[0]
            if resume_unverified(d,q,key,args)!='UNSAT_VERIFIED':deferred.add(key)
            continue
        summary=queue_summary(q)
        if summary['task_status']!='未完成任務':break
        pending=[key for key,node in q['nodes'].items() if node['status'] in ('PENDING','UNKNOWN','ERROR')]
        if not pending:break
        # Breadth-first queue is deterministic; every unresolved cube remains.
        key=min(pending,key=lambda k:(len(q['nodes'][k]['cube']),len(q['nodes'][k]['attempts']),k))
        slice_seconds=min(args.slice_seconds,remaining-2*args.check_seconds-30)
        path=make_attempt(d,q,key)
        try:
            process_result=launch_solver(args.solver,path/'instance.cnf',path/'proof.drat',path/'solver.log',slice_seconds,args.max_proof_bytes,
                                         getattr(args,'disk_reserve_bytes',0),getattr(args,'proof_expansion_factor',1.0))
            finish_attempt(d,q,m,key,path,process_result,args)
            if process_result.get('stop_reason')=='DISK_RESERVE_LIMIT':break
        except Exception as error:
            q['nodes'][key]['status']='ERROR';q['nodes'][key]['last_error']=repr(error)
            save_state(d,q);raise
    summary=queue_summary(q);save_state(d,q);atomic_json(d/'summary.json',summary)
    print(json.dumps(summary,ensure_ascii=False),flush=True)

def verify_state(args):
    d,q,m=load_state(args.state);nvars,base=read_dimacs(d/'base.cnf')
    # Replay the deterministic reduction as well as hashes. A changed encoder
    # cannot silently certify an earlier, differently encoded state.
    regenerated,metadata=encode(m['n'],m['squares'],m['parts'],m['amo'],m['pair_symmetry'],m['channel_reverse'],m['even_second_rows'])
    assert hashlib.sha256(regenerated.dimacs().encode()).hexdigest()==q['base_cnf_sha256']
    assert q['root']=='root' and q['nodes']['root']['cube']==[] and q['nodes']['root']['parent'] is None
    seen=set();certificate_replays=[]
    def visit(key,parent):
        assert key not in seen;seen.add(key);node=q['nodes'][key]
        assert node['parent']==parent
        cube=node['cube'];assert all(isinstance(x,int) and 0<abs(x)<=nvars for x in cube)
        assert len({abs(x) for x in cube})==len(cube)
        if node['status']=='SPLIT':
            lit=node['split_literal'];assert 0<abs(lit)<=nvars and abs(lit) not in {abs(x) for x in cube}
            left,right=node['children'];assert left!=right
            assert q['nodes'][left]['cube']==cube+[-lit] and q['nodes'][right]['cube']==cube+[lit]
            visit(left,key);visit(right,key);return
        assert node['status'] in ('PENDING','UNKNOWN','ERROR','RUNNING','UNSAT_UNVERIFIED','UNSAT_AWAITING_VERIFICATION','UNSAT_VERIFIED','SAT_VERIFIED')
        if node['status'] not in ('UNSAT_VERIFIED','SAT_VERIFIED'):return
        path=d/node['evidence'];result=json.loads(path.read_text());folder=path.parent
        assert result['status']==node['status'] and result['cube']==cube
        _,actual=read_dimacs(folder/'instance.cnf');assert actual==base+[[x] for x in cube]
        assert sha256_file(folder/'instance.cnf')==result['cnf_sha256']
        if node['status']=='SAT_VERIFIED':
            assert sha256_file(folder/result['witness'])==result['witness_sha256']
            witness=json.loads((folder/result['witness']).read_text())
            verify_squares(witness['squares']);verify_model_cnf(folder/'instance.cnf',witness['model'])
            assert decode_model(m,witness['model'])==witness['squares']
        else:
            checked=result['proof_check'];assert checked['status']=='UNSAT_VERIFIED'
            assert checked['cnf_sha256']==result['cnf_sha256']
            assert sha256_file(folder/checked['lrat'])==checked['lrat_sha256']
            replay=replay_lrat(folder/'instance.cnf',folder/checked['lrat'],args.lrat_check,folder/'replay-lrat.log',args.check_seconds)
            assert replay['verified'];certificate_replays.append({'node':key,**replay})
    visit('root',None);assert seen==set(q['nodes'])
    summary=queue_summary(q);summary['coverage_tree_verified']=True
    summary['lrat_certificates_replayed']=len(certificate_replays)
    atomic_json(d/'verification.json',summary)
    print(json.dumps(summary,ensure_ascii=False),flush=True)
    return summary

def validate(args):
    from pysat.solvers import Solver
    out=pathlib.Path(args.out);out.mkdir(parents=True,exist_ok=True);results=[]
    cases=[(2,1,(2,),True),(2,2,(2,),False),(3,2,(3,),True),(3,3,(3,),False),
           (4,3,(2,2),True),(4,3,(4,),False),(5,3,(5,),True)]
    for n,count,parts,expected in cases:
        folder=out/(f'n{n}_m{count}_'+'_'.join(map(str,parts)));folder.mkdir(exist_ok=True)
        m=write_instance(folder,n,count,parts);_,clauses=read_dimacs(folder/'base.cnf')
        with Solver(name='cadical195',bootstrap_with=clauses,with_proof=True) as solver:
            sat=solver.solve();assert sat==expected
            row={'n':n,'squares':count,'parts':parts,'sat':sat,'stats':solver.accum_stats(),
                 'cnf_sha256':sha256_file(folder/'base.cnf')}
            if sat:
                model=solver.get_model() or [];verify_model_cnf(folder/'base.cnf',model)
                witness=decode_model(m,model);atomic_json(folder/'witness.json',{'squares':witness,'model':model})
                row['status']='SAT_VERIFIED'
            else:
                proof=solver.get_proof() or []
                if not proof or proof[-1].strip()!='0':proof.append('0')
                (folder/'proof.drat').write_text('\n'.join(proof)+'\n')
                checked=verify_unsat(folder/'base.cnf',folder/'proof.drat',args.drat_trim,args.lrat_check,args.check_seconds)
                assert checked['status']=='UNSAT_VERIFIED',checked
                atomic_json(folder/'proof_check.json',checked);row['status']='UNSAT_VERIFIED';row['proof_check']=checked
            results.append(row);print(json.dumps(row),flush=True)
    # Exhaustive small-order projection test: enumerate every normalized
    # original SAT model for 3-MOLS(4), independently check it, then prove
    # that the unblocked original models are exhausted. Auxiliary assignments
    # cannot create duplicates because blockers use original positive cells.
    folder=out/'exhaustive_n4_m3';folder.mkdir(exist_ok=True)
    f,m=encode(4,3,(2,2));original_ids={v['id'] for v in m['variables'] if v['square'].startswith('L')}
    models=[];blockers=[]
    with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
        while solver.solve():
            model=solver.get_model();w=decode_model(m,model);models.append(w)
            block=[-x for x in model if x>0 and x in original_ids];assert block
            solver.add_clause(block);blockers.append(block)
    assert len(models)==len({json.dumps(x) for x in models})
    atomic_json(folder/'models.json',{'models':models,'blocking_clauses':blockers})
    (folder/'exhausted.cnf').write_text(f'p cnf {f.nvars} {len(f.clauses)+len(blockers)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in f.clauses+blockers))
    with Solver(name='cadical195',bootstrap_with=f.clauses+blockers,with_proof=True) as solver:
        assert not solver.solve();proof=solver.get_proof() or []
        if not proof or proof[-1].strip()!='0':proof.append('0')
        (folder/'proof.drat').write_text('\n'.join(proof)+'\n')
    checked=verify_unsat(folder/'exhausted.cnf',folder/'proof.drat',args.drat_trim,args.lrat_check,args.check_seconds)
    assert checked['status']=='UNSAT_VERIFIED';atomic_json(folder/'proof_check.json',checked)
    # Validate the actual parity gadget exhaustively on every permutation up
    # through order 6; SAT iff its directly counted inversion parity is even.
    parity_cases=0
    for n in range(2,7):
        f=Formula();cells=[[f.new() for _ in range(n)] for _ in range(n)]
        for row in cells:f.exactly_one(row)
        enforce_even_permutation(f,cells,[list(range(n)) for _ in range(n)])
        with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
            for perm in itertools.permutations(range(n)):
                sat=solver.solve(assumptions=[cells[c][perm[c]] for c in range(n)])
                assert sat==(sum(perm[c]>perm[d] for c,d in itertools.combinations(range(n),2))%2==0)
                parity_cases+=1
    # A full n=9 field construction exercises the simultaneous-even-row
    # normalization with n>2^3, unlike the n=4 and n=5 controls.
    def add(a,b):return ((a%3+b%3)%3)+3*((a//3+b//3)%3)
    def mul(a,b):return ((a%3*(b%3)-a//3*(b//3))%3)+3*((a%3*(b//3)+a//3*(b%3))%3)
    known=[[[add(mul(a,r),c) for c in range(9)] for r in range(9)] for a in (1,2,3)]
    verify_squares(known)
    f,m=encode(9,3,(3,3,3),even_second_rows=True)
    assumptions=[v['id'] for v in m['variables'] if v['square'].startswith('L') and known[int(v['square'][1:])][v['r']][v['c']]==v['value']]
    with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
        assert solver.solve(assumptions=assumptions);model=solver.get_model()
        assert decode_model(m,model)==known
    folder=out/'n9_even_positive';folder.mkdir(exist_ok=True)
    (folder/'base.cnf').write_text(f.dimacs());verify_model_cnf(folder/'base.cnf',model)
    atomic_json(folder/'witness.json',{'squares':known,'model':model})
    summary={'cases':results,'n4_m3_normalized_models_exhausted':len(models),
             'exhausted_formula_status':checked['status'],'checker_source':checked['checker_source'],
             'parity_gadget_permutations_checked':parity_cases,'n9_simultaneous_even_positive':'SAT_VERIFIED'}
    atomic_json(out/'summary.json',summary);print(json.dumps(summary),flush=True)

def handle_termination(signum,frame):
    # A bounded workflow wrapper sends SIGTERM to this Python process group.
    # Solver/checker children have their own groups, so unwind their cleanup
    # handlers before exiting; ignore a repeated TERM during that cleanup.
    signal.signal(signum,signal.SIG_IGN)
    raise SystemExit(128+signum)

def main():
    signal.signal(signal.SIGTERM,handle_termination)
    ap=argparse.ArgumentParser();commands=ap.add_subparsers(dest='command',required=True)
    p=commands.add_parser('init');p.add_argument('--state',required=True);p.add_argument('--n',type=int,default=10)
    p.add_argument('--squares',type=int,default=3);p.add_argument('--shard',type=int,default=0)
    p.add_argument('--amo',choices=['pairwise','sequential'],default='pairwise')
    p.add_argument('--even-row-normalization',action='store_true')
    p=commands.add_parser('run');p.add_argument('--state',required=True)
    p.add_argument('--seconds',type=float,default=18000);p.add_argument('--slice-seconds',type=float,default=3600)
    p.add_argument('--solver',default='kissat');p.add_argument('--max-proof-bytes',type=int,default=16*1024**3)
    p.add_argument('--disk-reserve-bytes',type=int,default=8*1024**3)
    p.add_argument('--proof-expansion-factor',type=float,default=3.0)
    p.add_argument('--split-lookahead',type=int,default=64)
    p.add_argument('--split-unknown',action=argparse.BooleanOptionalAction,default=True)
    p.add_argument('--drat-trim',default='drat-trim');p.add_argument('--lrat-check',default='lrat-check')
    p.add_argument('--check-seconds',type=float,default=900)
    p=commands.add_parser('verify');p.add_argument('--state',required=True)
    p.add_argument('--lrat-check',default='lrat-check');p.add_argument('--check-seconds',type=float,default=900)
    p=commands.add_parser('validate');p.add_argument('--out',required=True)
    p.add_argument('--drat-trim',default='drat-trim');p.add_argument('--lrat-check',default='lrat-check')
    p.add_argument('--check-seconds',type=float,default=60)
    p=commands.add_parser('manifest');p.add_argument('--n',type=int,default=10)
    p.add_argument('--squares',type=int,default=3);p.add_argument('--out',required=True)
    p.add_argument('--even-row-normalization',action='store_true')
    args=ap.parse_args()
    if args.command=='init':print(json.dumps(queue_summary(init_state(args)),ensure_ascii=False))
    elif args.command=='run':
        import fcntl
        pathlib.Path(args.state).mkdir(parents=True,exist_ok=True)
        with open(pathlib.Path(args.state)/'.writer.lock','a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            run_state(args)
    elif args.command=='verify':verify_state(args)
    elif args.command=='validate':validate(args)
    else:
        if args.even_row_normalization:assert args.n>2**args.squares
        rows=[]
        for i,parts in enumerate(partitions(args.n)):
            if args.even_row_normalization and (args.n-len(parts))%2:continue
            f,m=encode(args.n,args.squares,parts,even_second_rows=args.even_row_normalization)
            rows.append({'shard':i,'parts':list(parts),'cnf_sha256':hashlib.sha256(f.dimacs().encode()).hexdigest(),
                         'nvars':f.nvars,'clauses':len(f.clauses),'pair_representatives':[o['representative'] for o in m['pair_orbits']] if m['pair_orbits'] else []})
        manifest={'version':VERSION,'n':args.n,'squares':args.squares,
                  'normalization':'equal row-parity signature in all squares' if args.even_row_normalization else 'all derangement cycle types',
                  'even_row_normalization':args.even_row_normalization,'required_shards':rows,
                  'pair_representatives_total':sum(len(row['pair_representatives']) for row in rows),
                  'task_status':'未完成任務','coverage':'every solution has a representative in at least one listed shard; omitted odd shards are not asserted UNSAT'}
        atomic_json(args.out,manifest);print(json.dumps(manifest,ensure_ascii=False))

if __name__=='__main__':main()
