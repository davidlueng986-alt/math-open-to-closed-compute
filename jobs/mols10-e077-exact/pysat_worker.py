#!/usr/bin/env python3
"""Small-order validation backend. Production uses external streaming Kissat."""
import argparse,json,pathlib,time
from encode import read_dimacs
from pysat.solvers import Solver

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('cnf');p.add_argument('proof');p.add_argument('--solver',default='cadical195')
    a=p.parse_args();_,clauses=read_dimacs(a.cnf);start=time.monotonic()
    with Solver(name=a.solver,bootstrap_with=clauses,with_proof=True) as solver:
        sat=solver.solve()
        print('c pysat_stats '+json.dumps(solver.accum_stats()),flush=True)
        print('c wall_seconds '+str(time.monotonic()-start),flush=True)
        if sat:
            print('s SATISFIABLE',flush=True)
            model=solver.get_model() or []
            for i in range(0,len(model),20):print('v '+' '.join(map(str,model[i:i+20]))+' 0',flush=True)
            if not model:print('v 0',flush=True)
            raise SystemExit(10)
        proof=solver.get_proof() or []
        # For a contradiction already found during bootstrap, the empty
        # clause is directly RUP. An external checker still must validate it.
        if not proof or proof[-1].strip()!='0':proof.append('0')
        pathlib.Path(a.proof).write_text('\n'.join(proof)+'\n')
        print('s UNSATISFIABLE',flush=True)
        raise SystemExit(20)
