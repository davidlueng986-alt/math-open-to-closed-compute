"""Search for a counterexample to L-meta-3241 by exact AO2 circuit synthesis."""

import argparse
import json
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from itertools import permutations, product
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def representatives(p, q):
    """Enumerate non-isolated C4-free graphs up to shore-preserving isomorphism."""
    column_permutations = list(permutations(range(q)))
    encoded_rows = {
        row: tuple(sum(((row >> j) & 1) << i for i, j in enumerate(perm))
                   for perm in column_permutations)
        for row in range(1, 1 << q)
    }
    for rows in c4_free_rows(p, q):
        if any(rows > tuple(sorted(encoded_rows[row][k] for row in rows))
               for k in range(1, len(column_permutations))):
            continue
        yield tuple((i, p + j) for i, row in enumerate(rows)
                    for j in range(q) if row >> j & 1)


def c4_free_rows(p, q):
    def fill(rows, included):
        if len(rows) == p:
            if included == (1 << q) - 1:
                yield rows
            return
        for row in range(rows[-1] if rows else 1, 1 << q):
            if all((row & other).bit_count() <= 1 for other in rows):
                yield from fill((*rows, row), included | row)
    return fill((), 0)


def search(case):
    p, q, edges, conflicts = case
    n = p + q
    edge_bits = [1 << a | 1 << b for a, b in edges]
    independent = [mask for mask in range(1 << n)
                   if all(mask & edge != edge for edge in edge_bits)]
    maximum_independent = max(mask.bit_count() for mask in independent)
    star_cost = len(edges) + n - maximum_independent - 1
    gates = star_cost - 1
    if gates < n - 1:
        return case, 'support_bound', star_cost, None
    # A monotone function agrees everywhere if it agrees on these boundary inputs.
    independent_set = set(independent)
    maxima = [mask for mask in independent if all(
        mask & (1 << v) or mask | (1 << v) not in independent_set
        for v in range(n)
    )]
    examples = [(x, False) for x in maxima] + [(x, True) for x in edge_bits]
    pool = IDPool()
    selectors = []
    edge_set = set(edges)
    symmetries = []
    for a, b in product(permutations(range(p)), permutations(range(p, n))):
        order = a + b
        if {(order[i], order[j]) for i, j in edges} == edge_set:
            symmetries.append(order)
    with Solver(name='cadical195') as sat:
        for g in range(gates):
            available = n + g
            left = [pool.id((g, 'L', w)) for w in range(available)]
            right = [pool.id((g, 'R', w)) for w in range(available)]
            for sel in (left, right):
                sat.append_formula(CardEnc.equals(lits=sel, bound=1, vpool=pool,
                                                  encoding=EncType.seqcounter).clauses)
            for i in range(available):
                for j in range(i):
                    sat.add_clause([-left[i], -right[j]])
            if g == 0:
                for j in range(n):
                    for i in range(j + 1):
                        # Use the same operand ordering as the topological sort.
                        if any((j, i) > (max(order[i], order[j]), min(order[i], order[j]))
                               for order in symmetries):
                            sat.add_clause([-left[i], -right[j]])
            op = pool.id((g, 'OR'))
            if selectors:
                last_left, last_right, last_op = selectors[-1]
                # Canonical topological sort by larger input, then smaller input, then gate operation.
                for r, last in enumerate(last_right):
                    for smaller in range(r):
                        sat.add_clause([-last, -right[smaller]])
                    for i in range(r + 1):
                        for j in range(i):
                            sat.add_clause([-last, -right[r], -last_left[i], -left[j]])
                        sat.add_clause([-last, -right[r], -last_left[i], -left[i], -last_op])
                        sat.add_clause([-last, -right[r], -last_left[i], -left[i], op])
            selectors.append((left, right, op))
        for g in range(gates - 1):
            sat.add_clause([sel[n + g] for left, right, _ in selectors[g + 1:]
                            for sel in (left, right)])
        # Pad any shorter circuit to the budget by copying its output.
        padding = [pool.id((g, 'pad')) for g in range(gates)]
        sat.add_clause([-padding[0]])
        for g in range(1, gates):
            left, right, _ = selectors[g]
            sat.add_clause([-padding[g], left[-1]])
            sat.add_clause([-padding[g], right[-1]])
            sat.add_clause([-padding[g-1], padding[g]])
        witnesses = [[[], []] for _ in range(gates)]
        for mask, result in examples:
            values = [pool.id((mask, 'wire', w)) for w in range(n + gates)]
            for v in range(n):
                sat.add_clause([values[v] if mask >> v & 1 else -values[v]])
            for g, (left, right, is_or) in enumerate(selectors):
                a, b = (pool.id((mask, g, side)) for side in ('L','R'))
                for sel, value in ((left, a), (right, b)):
                    for w, chosen in enumerate(sel):
                        sat.add_clause([-chosen, -values[w], value])
                        sat.add_clause([-chosen, values[w], -value])
                z = values[n+g]
                sat.add_clause([-padding[g], z if result else -z])
                for j, (on, off) in enumerate(((a, b), (b, a))):
                    witness = pool.id((mask, g, 'diff', j))
                    sat.add_clause([-witness, on])
                    sat.add_clause([-witness, -off])
                    witnesses[g][j].append(witness)
                for clause in ([is_or, -a, -b, z], [is_or, a, -z], [is_or, b, -z],
                               [-is_or, a, b, -z], [-is_or, -a, z], [-is_or, -b, z]):
                    sat.add_clause(clause)
            sat.add_clause([values[-1] if result else -values[-1]])
        # Comparable operands make the gate redundant on the boundary inputs.
        # Every unpadded gate in a minimum circuit must have incomparable operands.
        for g, directions in enumerate(witnesses):
            for literals in directions:
                sat.add_clause([padding[g], *literals])
        sat.conf_budget(conflicts)
        solved = sat.solve_limited()
        if solved is None:
            return case, 'budget', star_cost, None
        if not solved:
            return case, 'unsat', star_cost, None
        model = set(sat.get_model())
        circuit = [('OR' if op in model else 'AND',
                    next(i for i, v in enumerate(left) if v in model),
                    next(i for i, v in enumerate(right) if v in model))
                   for left, right, op in selectors]
        for mask in range(1 << n):
            values = [(mask >> i) & 1 for i in range(n)]
            for op, a, b in circuit:
                values.append((values[a] | values[b]) if op == 'OR' else (values[a] & values[b]))
            assert values[-1] == any(mask & edge == edge for edge in edge_bits)
        return case, 'counterexample', star_cost, circuit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('points', type=int)
    parser.add_argument('lines', type=int)
    parser.add_argument('--conflicts', type=int, default=1_500_000)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not (1 <= args.points <= 6 and 1 <= args.lines <= 6):
        parser.error('shore sizes must be in 1–6')
    if args.workers < 1 or args.conflicts < 1:
        parser.error('workers and conflicts must be positive')

    # The excluded four-cycle has a 3-gate circuit against a 5-gate star cover.
    control = search((2, 2, ((0, 2), (0, 3), (1, 2), (1, 3)), 50_000))
    assert control[1] == 'counterexample' and control[2] == 5

    p, q = args.points, args.lines
    cases = [(p, q, edges, args.conflicts) for edges in representatives(p, q)]
    cases.sort(key=lambda case: len(case[2]))
    print(f'{p}x{q}: {len(cases)} graphs without isolated vertices', flush=True)
    counts = Counter()
    unresolved = []
    verified_witnesses = []
    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        for case, status, cost, circuit in executor.map(search, cases):
            counts[status] += 1
            row = {'edges': case[2], 'star_cost': cost}
            if status == 'budget':
                unresolved.append(row)
            if status == 'counterexample':
                verified_witnesses.append({**row, 'circuit': circuit})
                print(verified_witnesses[-1], flush=True)
    result = {
        'points': p, 'lines': q, 'conflicts_per_graph': args.conflicts,
        'counts': dict(counts), 'unresolved': unresolved,
        'counterexamples': verified_witnesses,
    }
    print(json.dumps(counts, sort_keys=True), flush=True)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
