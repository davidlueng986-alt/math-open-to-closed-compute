"""Plan, enumerate and compile complete finite reference SAT partitions.

The default command only writes metadata. Huge reference formulas are guarded.
Example: python -m finite_sat.reference manifest --out research/finite-sat-portfolio/manifest.json
"""
import argparse
import hashlib
import json
from pathlib import Path
from . import mols, moore, ramsey, partition
from .core import StreamCNF

TARGETS = {
    'RAMSEY-R3-10-N40': {'kind': 'ramsey', 'n': 40, 'r': 3, 's': 10},
    'RAMSEY-R5-5-N43': {'kind': 'ramsey', 'n': 43, 'r': 5, 's': 5},
    'RAMSEY-R5-5-N44': {'kind': 'ramsey', 'n': 44, 'r': 5, 's': 5},
    'RAMSEY-R5-5-N45': {'kind': 'ramsey', 'n': 45, 'r': 5, 's': 5},
    'MOLS10-3': {'kind': 'mols', 'n': 10, 'k': 3, 'normalize': True},
    'PROJECTIVE-PLANE-12': {'kind': 'plane', 'n': 12, 'k': 11, 'normalize': True},
    'MOORE-57': {'kind': 'moore', 'k': 57, 'normalize': True},
}


def split_keys(target):
    kind = TARGETS[target]['kind']
    if kind == 'ramsey':
        return [('edge', 0, j) for j in range(1, 5)]
    if kind == 'mols':
        return [('x', 0, 1, 1, 2), ('x', 0, 1, 2, 3),
                ('x', 1, 1, 0, 2), ('x', 2, 1, 0, 3)]
    if kind == 'plane':
        return [('x', 0, 1, 1, 0), ('x', 1, 2, 2, 0),
                ('x', 2, 3, 3, 0), ('x', 3, 4, 4, 0)]
    return moore.partition_keys(57)


def estimate(spec):
    if spec['kind'] == 'ramsey':
        return ramsey.counts(spec['n'], spec['r'], spec['s'])
    if spec['kind'] in ('mols', 'plane'):
        return mols.counts(spec['n'], spec['k'], spec['normalize'])
    value = moore.estimate(spec['k'], spec['normalize'])
    return {**value, 'variables': value['primary_variables']}


def emit(builder, spec):
    if spec['kind'] == 'ramsey':
        return ramsey.emit(builder, spec['n'], spec['r'], spec['s'])
    if spec['kind'] in ('mols', 'plane'):
        result = mols.emit(builder, spec['n'], spec['k'], spec['normalize'])
        result['original_kind'] = spec['kind']
        return result
    return moore.emit(builder, spec['k'], spec['normalize'])


def manifest():
    source_dir = Path(__file__).parent
    sources = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted(source_dir.glob('*.py'))}
    roots = []
    for target, spec in TARGETS.items():
        keys = split_keys(target)
        terminal = partition.leaves(keys)
        partition.validate_cover(keys, terminal)
        roots.append({'id': target, 'spec': spec, 'size_before_cube': estimate(spec),
                      'split_keys': [list(k) for k in keys],
                      'leaves': [{**leaf, 'status': 'OPEN'} for leaf in terminal],
                      'sat_rule': 'one independently verified original witness',
                      'unsat_rule': 'all terminal exact-CNF proofs replayed AND complete cover checked'})
    return {'schema_version': 'finite-sat-reference-portfolio-v1',
            'source_sha256': sources, 'decision_roots': roots,
            'decision_root_count': len(roots), 'reference_leaf_count': sum(len(r['leaves']) for r in roots),
            'status': 'FORMULATED_NOT_SOLVED',
            'scope': 'Four newly selected famous targets plus existing R(3,10); existing optimized queues preserved.',
            'ramsey55_exact_rule': {
                'imports': {'SAT_42': 'Exoo witness', 'UNSAT_46': 'Angeltveit-McKay theorem'},
                'start': 44, 'if_44_unsat_query': 43, 'if_44_sat_query': 45,
                'cases': [{'answer': 43, 'need': ['UNSAT_43']},
                          {'answer': 44, 'need': ['SAT_43', 'UNSAT_44']},
                          {'answer': 45, 'need': ['SAT_44', 'UNSAT_45']},
                          {'answer': 46, 'need': ['SAT_45']}]},
            'historical_progress_is_separate': True}


def compile_leaf(target, word, out, max_clauses=5_000_000):
    spec = TARGETS[target]
    size = estimate(spec)
    choices = {l['id']: l for l in partition.leaves(split_keys(target))}
    if word not in choices:
        raise ValueError('unknown leaf word')
    if size['clauses'] + 4 > max_clauses:
        raise ValueError(f"reference size {size['clauses']:,} clauses exceeds explicit limit {max_clauses:,}; use an optimized complete route or an intentional larger limit")
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    cnf = StreamCNF(out / 'instance.cnf')
    metadata = emit(cnf, spec)
    if cnf.nvars != size['variables'] or cnf.nclauses != size['clauses']:
        raise AssertionError('generator/count mismatch')
    for clause in partition.units(cnf, choices[word]):
        cnf.add(clause)
    digest = cnf.finish()
    data = {'target': target, 'spec': spec, 'leaf': choices[word],
            'variables': cnf.nvars, 'clauses': cnf.nclauses,
            'cnf_sha256': digest, 'metadata': metadata,
            'generator_sha256': manifest()['source_sha256']}
    (out / 'instance.json').write_text(json.dumps(data, indent=2) + '\n')
    return {k: data[k] for k in ('target', 'variables', 'clauses', 'cnf_sha256')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    cmd = commands.add_parser('manifest')
    cmd.add_argument('--out', required=True)
    cmd = commands.add_parser('estimate')
    cmd.add_argument('--target', choices=TARGETS)
    cmd = commands.add_parser('compile')
    cmd.add_argument('--target', choices=TARGETS, required=True)
    cmd.add_argument('--leaf', required=True)
    cmd.add_argument('--out', required=True)
    cmd.add_argument('--max-clauses', type=int, default=5_000_000)
    args = parser.parse_args()
    if args.command == 'manifest':
        result = manifest()
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out).write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps({'roots': result['decision_root_count'], 'leaves': result['reference_leaf_count'], 'out': args.out}))
    elif args.command == 'estimate':
        print(json.dumps({k: estimate(v) for k, v in TARGETS.items() if not args.target or k == args.target}, indent=2))
    else:
        print(json.dumps(compile_leaf(args.target, args.leaf, args.out, args.max_clauses), indent=2))


if __name__ == '__main__':
    main()
