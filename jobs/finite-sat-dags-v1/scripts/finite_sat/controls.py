"""Semantic controls plus optional real Kissat/DRAT replay on tiny instances.

All production target roots remain OPEN. This validates software and covers.
"""
import argparse
import json
from itertools import combinations, product
from pathlib import Path
from .core import MemoryCNF
from . import mols, moore, plane, ramsey, partition, reference
from .certificate import solve_and_check


def semantic_controls():
    report = {}
    # Exhaustive original graph semantics, not a second CNF generator.
    count = 0
    for n, r, s in ((4, 3, 3), (5, 3, 3), (5, 3, 4)):
        builder = MemoryCNF()
        meta = ramsey.emit(builder, n, r, s)
        for bits in product((False, True), repeat=builder.nvars):
            model = [i+1 if b else -(i+1) for i, b in enumerate(bits)]
            graph = [[0]*n for _ in range(n)]
            for i, j, v in meta['edges']:
                graph[i][j] = graph[j][i] = int(bits[v-1])
            assert builder.satisfied(model) == ramsey.verify(graph, r, s)['valid']
            count += 1
    report['exhaustive_ramsey_graphs'] = count
    report['plane_controls'] = plane.self_test()
    report['moore_controls'] = moore.self_test()
    # Known complete MOLS; independently checked constructive assignments satisfy
    # the actual emitted clauses, before and after the allowed normalization.
    latin = []
    for n in (2, 3, 5):
        squares = [[[(a*r+c) % n for c in range(n)] for r in range(n)] for a in range(1,n)]
        squares = mols.normalize(squares)
        b = MemoryCNF()
        meta = mols.emit(b, n, n-1)
        model = mols.witness_assignment(squares, b)
        assert b.satisfied(model)
        assert mols.decode(model, meta) == squares
        latin.append({'n':n, 'k':n-1, 'variables':b.nvars, 'clauses':b.nclauses})
    report['constructive_mols_controls'] = latin
    manifest = reference.manifest()
    for root in manifest['decision_roots']:
        assert partition.validate_cover(root['split_keys'], root['leaves'])
        assert partition.assemble(root['split_keys'], root['leaves']) == 'OPEN'
        try:
            partition.validate_cover(root['split_keys'], root['leaves'][:-1])
        except ValueError:
            pass
        else:
            raise AssertionError('missing leaf accepted')
        duplicate = root['leaves'][:-1] + [root['leaves'][0]]
        try:
            partition.validate_cover(root['split_keys'], duplicate)
        except ValueError:
            pass
        else:
            raise AssertionError('duplicate leaf accepted')
    report['complete_target_partitions'] = len(manifest['decision_roots'])
    report['reference_leaf_count'] = manifest['reference_leaf_count']
    from .ramsey_boundary import exact_value
    for decisions, expected in (({43:'UNSAT'},43),({43:'SAT',44:'UNSAT'},44),
                                ({44:'SAT',45:'UNSAT'},45),({45:'SAT'},46)):
        assert exact_value(42,46,decisions)['exact'] == expected
    assert exact_value(42,46,{43:'SAT'})['exact'] is None
    try:
        exact_value(42,46,{44:'UNSAT',45:'SAT'})
    except ValueError:
        pass
    else:
        raise AssertionError('contradictory Ramsey decisions accepted')
    report['ramsey_exact_value_rules'] = 'PASS: four boundaries, partial evidence and contradiction rejection'
    report['status'] = 'PASS'
    return report


def proof_controls(out):
    out = Path(out)
    cases = [
        ('ramsey-3-3-n5', {'kind':'ramsey','n':5,'r':3,'s':3}, 'VERIFIED_SAT'),
        ('ramsey-3-3-n6', {'kind':'ramsey','n':6,'r':3,'s':3}, 'VERIFIED_UNSAT'),
        ('mols-2-1', {'kind':'mols','n':2,'k':1,'normalize':True}, 'VERIFIED_SAT'),
        ('mols-2-2', {'kind':'mols','n':2,'k':2,'normalize':True}, 'VERIFIED_UNSAT'),
        ('mols-3-3', {'kind':'mols','n':3,'k':3,'normalize':True}, 'VERIFIED_UNSAT'),
        ('plane-3', {'kind':'plane','n':3,'k':2,'normalize':True}, 'VERIFIED_SAT'),
        ('moore-2', {'kind':'moore','k':2,'normalize':True}, 'VERIFIED_SAT'),
        ('moore-3', {'kind':'moore','k':3,'normalize':True}, 'VERIFIED_SAT'),
        ('moore-4', {'kind':'moore','k':4,'normalize':True}, 'VERIFIED_UNSAT'),
    ]
    results = []
    for name, spec, expected in cases:
        builder = MemoryCNF()
        metadata = reference.emit(builder, spec)
        result = solve_and_check(builder, metadata, spec, out/name)
        if result['status'] != expected:
            raise AssertionError(f'{name}: {result}')
        results.append({'case':name, 'expected':expected, **result})
    # Actual complete all-UNSAT partition: 16 separate replayed leaf proofs.
    spec = {'kind':'ramsey','n':6,'r':3,'s':3}
    b = MemoryCNF()
    meta = reference.emit(b, spec)
    keys = [('edge',0,j) for j in range(1,5)]
    leaves = partition.leaves(keys)
    verified = []
    for leaf in leaves:
        result = solve_and_check(b,meta,spec,out/'partition-r336'/leaf['id'],partition.units(b,leaf))
        assert result['status'] == 'VERIFIED_UNSAT'
        verified.append(leaf['id'])
    assert partition.assemble(keys,leaves,checked_unsat=verified) == 'UNSAT'
    assert partition.assemble(keys,leaves,checked_unsat=verified[:-1]) == 'OPEN'
    # Verify that a foreign CNF cannot inherit a checked proof by its status.
    from .certificate import replay_unsat
    d=out/'ramsey-3-3-n6'
    try:
        replay_unsat(d/'instance.cnf',d/'proof.drat','0'*64,'0'*64,d/'must-not-run.log')
    except ValueError:
        pass
    else:
        raise AssertionError('foreign proof binding accepted')
    return {'status':'PASS','cases':results,'all_unsat_cover':{'leaves':16,'checked':16},
            'missing_proof_stays_open':True,'foreign_hash_rejected':True,
            'production_targets_solved':0}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',required=True)
    parser.add_argument('--with-solvers',action='store_true')
    args=parser.parse_args()
    out=Path(args.out)
    out.mkdir(parents=True,exist_ok=True)
    result={'semantic':semantic_controls()}
    if args.with_solvers:
        result['proof_controls']=proof_controls(out/'proof-controls')
    result['status']='PASS'
    (out/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
