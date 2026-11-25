"""Synthesize local replacements for the order-3 plane incidence circuit."""
import argparse
import json
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

DIFF = (0, 1, 3, 9)


def graph(lines):
    neighborhoods = [sorted((line + offset) % 13 for offset in DIFF) for line in lines]
    points = sorted({point for row in neighborhoods for point in row})
    edges = [(points.index(point), len(points) + j)
             for j, row in enumerate(neighborhoods) for point in row]
    n = len(points) + len(lines)
    return n, edges, (points.index(0), len(points) + lines.index(0))


def evaluate(n, gates, input_mask, marked=None):
    vals = [bool(input_mask >> i & 1) for i in range(n)]
    traces = [i == marked for i in range(n)]
    for is_or, a, b in gates:
        va, vb = vals[a], vals[b]
        da, db = traces[a], traces[b]
        vals.append(va or vb if is_or else va and vb)
        traces.append(da or db if is_or else (va and db) or (da and vb))
    return vals[-1], traces[-1]


def synthesize(n, edges, flag, k, limit):
    edge_masks = [1 << a | 1 << b for a, b in edges]
    def target(mask):
        return any(mask & edge == edge for edge in edge_masks)
    independent = {mask for mask in range(1 << n) if not target(mask)}
    negatives = [mask for mask in sorted(independent) if all(
        mask & (1 << i) or mask | (1 << i) not in independent for i in range(n)
    )]
    examples = [(mask, True, None) for mask in edge_masks]
    examples += [(mask, False, None) for mask in negatives]
    examples += [(1 << flag[0], False, flag[1]), (1 << flag[1], False, flag[0])]
    pool = IDPool()
    selectors = []
    with Solver(name='cadical195') as sat:
        def or_relation(a, b, z):
            sat.append_formula([[a, b, -z], [-a, z], [-b, z]])
        def and_relation(a, b, z):
            sat.append_formula([[-a, -b, z], [a, -z], [b, -z]])
        def mux(choices, values, output):
            for choose, value in zip(choices, values):
                sat.add_clause([-choose, -value, output])
                sat.add_clause([-choose, value, -output])
        for g in range(k):
            available = n + g
            left = [pool.id(('left', g, w)) for w in range(available)]
            right = [pool.id(('right', g, w)) for w in range(available)]
            op = pool.id(('or', g))
            for choice in (left, right):
                sat.append_formula(CardEnc.equals(lits=choice, bound=1, vpool=pool,
                                                  encoding=EncType.seqcounter).clauses)
            for a in range(available):
                for b in range(a + 1):
                    sat.add_clause([-left[a], -right[b]])
            if selectors:
                prev_left, prev_right, prev_op = selectors[-1]
                for b, before in enumerate(prev_right):
                    for lower in range(b):
                        sat.add_clause([-before, -right[lower]])
                    for a in range(b):
                        for lower in range(a):
                            sat.add_clause([-before, -right[b], -prev_left[a], -left[lower]])
                        sat.add_clause([-before, -right[b], -prev_left[a], -left[a], -prev_op, op])
            selectors.append((left, right, op))
        for g in range(k - 1):
            sat.add_clause([sel[n + g] for left, right, _ in selectors[g + 1:]
                            for sel in (left, right)])
        for sample, (mask, expected, marked) in enumerate(examples):
            vals = [pool.id(('value', sample, i)) for i in range(n + k)]
            for i, v in enumerate(vals[:n]):
                sat.add_clause([v if mask >> i & 1 else -v])
            traces = None
            if marked is not None:
                traces = [pool.id(('trace', sample, i)) for i in range(n + k)]
                for i, v in enumerate(traces[:n]):
                    sat.add_clause([v if i == marked else -v])
            for g, (left, right, op) in enumerate(selectors):
                a, b = (pool.id(('operand', sample, g, arm)) for arm in range(2))
                mux(left, vals, a)
                mux(right, vals, b)
                z = vals[n + g]
                sat.append_formula([[op, -a, -b, z], [op, a, -z], [op, b, -z],
                                    [-op, a, b, -z], [-op, -a, z], [-op, -b, z]])
                if traces is None:
                    continue
                da, db, t1, t2, t_and, t_or = [pool.id(('d', sample, g, role)) for role in range(6)]
                mux(left, traces, da)
                mux(right, traces, db)
                and_relation(a, db, t1)
                and_relation(da, b, t2)
                or_relation(t1, t2, t_and)
                or_relation(da, db, t_or)
                d = traces[n + g]
                sat.append_formula([[op, -t_and, d], [op, t_and, -d],
                                    [-op, -t_or, d], [-op, t_or, -d]])
            sat.add_clause([vals[-1] if expected else -vals[-1]])
            if traces is not None:
                sat.add_clause([-traces[-1]])
        sat.conf_budget(limit)
        result = sat.solve_limited()
        if result is None:
            return 'budget', None
        if not result:
            return 'unsat', None
        model = set(sat.get_model())
        circ = [(op in model, next(i for i, v in enumerate(left) if v in model),
                 next(i for i, v in enumerate(right) if v in model)) for left, right, op in selectors]
        assert all(evaluate(n, circ, mask)[0] == target(mask) for mask in range(1 << n))
        assert not evaluate(n, circ, 1 << flag[0], flag[1])[1]
        assert not evaluate(n, circ, 1 << flag[1], flag[0])[1]
        return 'verified', circ


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('lines', type=int, nargs='+')
    p.add_argument('--gates', type=int)
    p.add_argument('--conflicts', type=int, default=750_000)
    args = p.parse_args()
    if 0 not in args.lines or len(set(args.lines)) != len(args.lines):
        p.error('line indices must be distinct and include line 0')
    if any(not 0 <= line < 13 for line in args.lines):
        p.error('line indices must be between 0 and 12')
    if args.conflicts < 1 or (args.gates is not None and args.gates < 1):
        p.error('gates and conflicts must be positive')
    n, edges, flag = graph(args.lines)
    size = args.gates if args.gates is not None else len(edges) + len(args.lines) - 1
    print(json.dumps({'lines': args.lines, 'inputs': n, 'edges': len(edges), 'gates': size}), flush=True)
    outcome, circ = synthesize(n, edges, flag, size, args.conflicts)
    print(json.dumps({'outcome': outcome, 'circuit': circ}), flush=True)
