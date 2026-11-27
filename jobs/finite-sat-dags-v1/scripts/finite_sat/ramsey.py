"""Exact unrestricted Ramsey existence formula, with an independent checker."""
from itertools import combinations
from math import comb


def counts(n, r, s):
    if any(type(x) is not int for x in (n, r, s)) or n < 1 or min(r, s) < 2:
        raise ValueError('need integer n>=1, r,s>=2')
    return {'variables': comb(n, 2), 'clauses': comb(n, r) + comb(n, s)}


def emit(builder, n, r, s):
    expected = counts(n, r, s)
    edges = {(i, j): builder.var(('edge', i, j)) for i, j in combinations(range(n), 2)}
    for vertices in combinations(range(n), r):
        builder.add(-edges[e] for e in combinations(vertices, 2))
    for vertices in combinations(range(n), s):
        builder.add(edges[e] for e in combinations(vertices, 2))
    return {'kind': 'ramsey', 'encoding': 'ramsey-unrestricted-v1', 'n': n, 'r': r, 's': s,
            'edges': [[i, j, v] for (i, j), v in edges.items()],
            'primary_variables': list(edges.values()),
            'expected_variables': expected['variables'], 'expected_clauses': expected['clauses']}


def clique_witness(rows, size):
    """Exact branch-and-bound over bitsets, independent of clause enumeration."""
    def search(candidates, chosen):
        need = size - len(chosen)
        if need == 0:
            return chosen
        while candidates.bit_count() >= need:
            bit = candidates & -candidates
            candidates ^= bit
            v = bit.bit_length() - 1
            found = search(candidates & rows[v], chosen + [v])
            if found is not None:
                return found
        return None
    return search((1 << len(rows)) - 1, [])


def verify(graph, r, s, expected_n=None):
    n = len(graph)
    if expected_n is not None and n != expected_n:
        return {'valid': False, 'reason': 'wrong vertex count'}
    if any(len(row) != n for row in graph):
        return {'valid': False, 'reason': 'non-square adjacency'}
    if any(type(graph[i][j]) not in (int, bool) or graph[i][j] not in (0, 1)
           for i in range(n) for j in range(n)):
        return {'valid': False, 'reason': 'non-binary adjacency'}
    if any(graph[i][i] for i in range(n)) or any(graph[i][j] != graph[j][i]
            for i in range(n) for j in range(i)):
        return {'valid': False, 'reason': 'loops or asymmetric adjacency'}
    rows = [sum(int(graph[i][j]) << j for j in range(n)) for i in range(n)]
    clique = clique_witness(rows, r)
    mask = (1 << n) - 1
    independent = clique_witness([mask ^ rows[i] ^ (1 << i) for i in range(n)], s)
    return {'valid': clique is None and independent is None, 'n': n, 'r': r, 's': s,
            'forbidden_clique': clique, 'forbidden_independent_set': independent}


def decode(model, metadata):
    positive = {x for x in model if x > 0}
    n = metadata['n']
    graph = [[0] * n for _ in range(n)]
    for i, j, v in metadata['edges']:
        graph[i][j] = graph[j][i] = int(v in positive)
    result = verify(graph, metadata['r'], metadata['s'], n)
    if not result['valid']:
        raise ValueError(result)
    return graph
