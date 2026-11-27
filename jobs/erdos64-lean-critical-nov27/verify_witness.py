#!/usr/bin/env python3
"""Independent finite audit of the 14-vertex path-consequence obstruction.

This verifies one exact graph; it is not a graph census or original closure.
The Lean source independently certifies the mathematical statements using
actual SimpleGraph walks, kernel reduction and the finite cycle-order bound.
"""
from __future__ import annotations
import argparse
from collections import Counter
import json
from pathlib import Path


def audit(w: dict) -> dict:
    n = w['order']
    assert n == 14
    edges = [tuple(e) for e in w['edges']]
    assert all(0 <= u < v < n for u, v in edges)
    assert len(set(edges)) == len(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    degrees = [len(s) for s in adj]
    assert degrees == w['degrees']
    assert min(degrees) == 2 and max(degrees) == 3
    assert degrees.count(2) == 6

    cycles = set()
    for start in range(n):
        def visit(path):
            for v in adj[path[-1]]:
                if v == start and len(path) >= 3 and path[1] < path[-1]:
                    cycles.add(tuple(path))
                elif v > start and v not in path:
                    visit(path + [v])
        visit([start])
    assert cycles == {tuple(c) for c in w['cycles']}
    cycle_lengths = sorted({len(c) for c in cycles})
    assert cycle_lengths == [6, 7, 9, 10, 11, 12, 14]
    assert 3 not in cycle_lengths
    assert all(k & (k - 1) for k in cycle_lengths)

    pairs = set()
    exits = {}
    for cert in w['pair_exit_paths']:
        p = cert['path']
        u, v, exit_vertex = cert['source'], cert['target'], cert['exit']
        assert p[0] == u and p[-1] == v and p[1] == exit_vertex
        assert len(p) == len(set(p))
        assert len(p) - 1 in (4, 8)
        assert all(y in adj[x] for x, y in zip(p, p[1:]))
        pairs.add((u, v))
        exits.setdefault((u, v), set()).add(exit_vertex)
    assert pairs == {(u, v) for u in range(n) for v in range(n) if u != v}
    distant = {(u, v) for u, v in pairs if v not in adj[u] and not (adj[u] & adj[v])}
    assert all(len(exits[p]) >= 2 for p in distant)

    fermat_p3, plus_two_p3 = set(), set()
    for c in cycles:
        for i, x in enumerate(c):
            a, b = sorted((c[i-1], c[(i+1) % len(c)]))
            if len(c) == 9:
                fermat_p3.add((x, a, b))
            if len(c) in (6, 10):
                plus_two_p3.add((x, a, b))
    all_p3 = {(x, a, b) for x in range(n) for a in adj[x] for b in adj[x] if a < b}
    assert all_p3 <= fermat_p3 and all_p3 <= plus_two_p3

    # Extra ordinary finite check; not asserted as a Lean theorem in this package.
    biconnected = True
    for deleted in range(n):
        start = next(v for v in range(n) if v != deleted)
        seen, stack = {start}, [start]
        while stack:
            for v in adj[stack.pop()] - seen - {deleted}:
                seen.add(v)
                stack.append(v)
        biconnected &= len(seen) == n - 1
    assert biconnected
    return {
        'scope': 'One exact obstruction to a proposed path-consequence closure implication; not original or terminal closure.',
        'order': n,
        'edge_count': len(edges),
        'degree_counts': dict(sorted(Counter(degrees).items())),
        'all_simple_cycle_count': len(cycles),
        'cycle_length_counts': dict(sorted(Counter(map(len, cycles)).items())),
        'all_unordered_pairs': len(pairs) // 2,
        'distant_unordered_pairs_with_two_exits_at_each_end': len(distant) // 2,
        'induced_p3_count': len(all_p3),
        'all_p3_on_9_cycle': True,
        'all_p3_on_6_or_10_cycle': True,
        'no_power_cycle': True,
        'not_near': True,
        'biconnected_python_only': biconnected,
        'status': 'PASS'
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--witness', type=Path, default=Path(__file__).resolve().parent / 'witness14.json')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = audit(json.loads(args.witness.read_text()))
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
