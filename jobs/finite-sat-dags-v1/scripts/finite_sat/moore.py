"""Exact reference CNF for diameter-two Moore graphs.

The normalized degree-57 formula is finite but far too large to emit blindly:
use estimate(57), not emit(..., 57), for planning.  The implementation is a
correctness baseline.  It makes no cyclic, group, or automorphism assumption.

Builder protocol: var(hashable_key) -> positive integer; add(iterable[int]).
Vertex representation returned by decode: sorted adjacency lists, not a matrix.
"""
from itertools import combinations, permutations, product
from math import comb


def _choose(n, r):
    return comb(n, r) if n >= r else 0


def estimate(k, normalize=True):
    if not isinstance(k, int) or isinstance(k, bool) or k < 2:
        raise ValueError("k must be an integer >= 2")
    m = k - 1
    t = k - 1 if normalize else k
    counts = {
        "vertices": k * k + 1,
        "edges_in_witness": (k * k + 1) * k // 2,
        "primary_variables": _choose(t, 2) * m * m,
        "matching_clauses": _choose(t, 2) * 2 * m * (1 + _choose(m, 2)),
        "derangement_units": _choose(t, 2) * m if normalize else 0,
        "four_cycles_through_group_zero": 3 * _choose(t, 3) * m * m if normalize else 0,
        "triangles_without_group_zero": _choose(t, 3) * m ** 3,
        "four_cycles_without_group_zero": 3 * _choose(t, 4) * m ** 4,
    }
    counts["clauses"] = sum(counts[x] for x in (
        "matching_clauses", "derangement_units", "four_cycles_through_group_zero",
        "triangles_without_group_zero", "four_cycles_without_group_zero"))
    counts["normalize"] = normalize
    counts["auxiliary_variables"] = 0
    return counts


def _key(i, j, a, b):
    if i == j:
        raise ValueError("edge variables join distinct groups")
    return ("moore", i, j, a, b) if i < j else ("moore", j, i, b, a)


def partition_keys(k):
    """Four documented primary split variables, fewer for tiny controls."""
    estimate(k)
    if k >= 9:
        return [("moore", 1, 2, 0, 1), ("moore", 1, 3, 2, 3),
                ("moore", 2, 3, 4, 5), ("moore", 2, 4, 6, 7)]
    keys = [_key(i, j, a, b) for i, j in combinations(range(1, k), 2)
            for a in range(k - 1) for b in range(k - 1) if a != b]
    return keys[:4]


def emit(builder, k, normalize=True):
    """Emit the full exact baseline CNF and return compact planning metadata.

    There is no internal production-size guard: callers must consult estimate.
    All variables are allocated deterministically before clauses.  Fixed edges
    incident to group zero are represented in the decoder, never omitted from
    the mathematical graph.  Clause counts include redundant/duplicate clauses.
    """
    meta = estimate(k, normalize)
    m = k - 1
    groups = range(1 if normalize else 0, k)
    primary = [] if k <= 7 else None
    split_candidates = []
    for i, j in combinations(groups, 2):
        for a in range(m):
            for b in range(m):
                v = builder.var(_key(i, j, a, b))
                if primary is not None:
                    primary.append(v)
                if (not normalize or a != b) and len(split_candidates) < 64:
                    split_candidates.append(v)

    def edge(i, j, a, b):
        return builder.var(_key(i, j, a, b))

    def exactly_one(row):
        builder.add(row)
        for x, y in combinations(row, 2):
            builder.add([-x, -y])

    for i, j in combinations(groups, 2):
        for a in range(m):
            exactly_one([edge(i, j, a, b) for b in range(m)])
        for b in range(m):
            exactly_one([edge(i, j, a, b) for a in range(m)])
        if normalize:
            # A diagonal edge would close a triangle through group zero.
            for a in range(m):
                builder.add([-edge(i, j, a, a)])

    for i, j, h in combinations(groups, 3):
        if normalize:
            # Three distinct undirected 4-cycles on groups {0,i,j,h}.
            # Group zero and its two neighboring groups share label a.
            for left, middle, right in ((i, j, h), (i, h, j), (j, i, h)):
                for a, b in product(range(m), repeat=2):
                    builder.add([-edge(left, middle, a, b),
                                 -edge(middle, right, b, a)])
        for a, b, c in product(range(m), repeat=3):
            builder.add([-edge(i, j, a, b), -edge(j, h, b, c),
                         -edge(h, i, c, a)])

    for i, j, h, ell in combinations(groups, 4):
        # The three undirected Hamilton cycles of four distinct groups.
        for u, v, w, z in ((i, j, h, ell), (i, j, ell, h), (i, h, j, ell)):
            for a, b, c, d in product(range(m), repeat=4):
                builder.add([-edge(u, v, a, b), -edge(v, w, b, c),
                             -edge(w, z, c, d), -edge(z, u, d, a)])

    meta["split_candidates"] = split_candidates
    if primary is not None:
        meta["primary_variable_ids"] = primary
    meta["encoding"] = "moore-rooted-matchings-reference-v1"
    return meta


def decode(builder, positive_assignment, k, normalize=True):
    """Reconstruct the original graph; always call verify on this result."""
    estimate(k, normalize)
    positive = set(v for v in positive_assignment if v > 0)
    m = k - 1
    adj = [set() for _ in range(k * k + 1)]

    def connect(u, v):
        adj[u].add(v)
        adj[v].add(u)

    def leaf(i, a):
        return 1 + k + i * m + a

    for i in range(k):
        connect(0, 1 + i)
        for a in range(m):
            connect(1 + i, leaf(i, a))
    for i, j in combinations(range(k), 2):
        for a in range(m):
            for b in range(m):
                present = (a == b) if normalize and i == 0 else (
                    builder.var(_key(i, j, a, b)) in positive)
                if present:
                    connect(leaf(i, a), leaf(j, b))
    return [sorted(row) for row in adj]


def verify(graph, k):
    """Independent direct check of srg(k^2+1,k,0,1), no CNF assumptions."""
    if not isinstance(k, int) or isinstance(k, bool) or k < 2:
        return False
    n = k * k + 1
    if not isinstance(graph, (list, tuple)) or len(graph) != n:
        return False
    rows = []
    for u, row in enumerate(graph):
        if not isinstance(row, (list, tuple, set, frozenset)):
            return False
        if len(row) != k or any(type(v) is not int or v < 0 or v >= n for v in row):
            return False
        neighbors = set(row)
        if len(neighbors) != k or u in neighbors:
            return False
        rows.append(neighbors)
    for u, row in enumerate(rows):
        if any(u not in rows[v] for v in row):
            return False
    for u, v in combinations(range(n), 2):
        if len(rows[u] & rows[v]) != (0 if v in rows[u] else 1):
            return False
    return True


def control_graph(k):
    """Explicit normalized C5/Petersen fixtures, independent of a SAT solver."""
    if k not in (2, 3):
        raise ValueError("controls are provided for k=2 and k=3")
    m = k - 1
    adj = [set() for _ in range(k * k + 1)]

    def link(a, b):
        adj[a].add(b)
        adj[b].add(a)

    def leaf(i, a):
        return 1 + k + i * m + a

    for i in range(k):
        link(0, 1 + i)
        for a in range(m):
            link(1 + i, leaf(i, a))
    for j in range(1, k):
        for a in range(m):
            link(leaf(0, a), leaf(j, a))
    if k == 3:
        for a in range(2):
            link(leaf(1, a), leaf(2, 1 - a))
    return [sorted(row) for row in adj]


def self_test():
    """Finite semantic controls, not a proof about degree 57."""
    class Recording:
        def __init__(self):
            self.keys = {}
            self.clauses = []

        def var(self, key):
            if key not in self.keys:
                self.keys[key] = len(self.keys) + 1
            return self.keys[key]

        def add(self, clause):
            self.clauses.append(tuple(clause))

    def satisfies(builder, positive):
        return all(any((x in positive) if x > 0 else (-x not in positive)
                       for x in clause) for clause in builder.clauses)

    results = {}
    for k in (2, 3, 4, 7):
        b = Recording()
        e = emit(b, k)
        assert len(b.keys) == e["primary_variables"]
        assert len(b.clauses) == e["clauses"]
        results[str(k)] = {"variables": len(b.keys), "clauses": len(b.clauses)}
        if k in (2, 3):
            assert verify(control_graph(k), k)
            positives = []
            for mask in range(1 << len(b.keys)):
                p = {i + 1 for i in range(len(b.keys)) if mask >> i & 1}
                sat = satisfies(b, p)
                graph = decode(b, p, k)
                assert sat == verify(graph, k)
                if sat:
                    positives.append(p)
            assert len(positives) == 1
            assert decode(b, positives[0], k) == control_graph(k)
            results[str(k)]["satisfying_assignments"] = len(positives)
        if k == 4:
            # Every normalized matching must be a derangement.  These eight
            # complete candidates exhaust the matching clauses for k=4.
            derangements = [p for p in permutations(range(3))
                            if all(p[a] != a for a in range(3))]
            tried = 0
            for choices in product(derangements, repeat=3):
                p = set()
                for (i, j), perm in zip(combinations(range(1, 4), 2), choices):
                    p.update(b.var(_key(i, j, a, perm[a])) for a in range(3))
                assert not satisfies(b, p)
                assert not verify(decode(b, p, k), k)
                tried += 1
            assert tried == 8
            results[str(k)]["exhaustive_matching_candidates"] = tried
            results[str(k)]["satisfying_assignments"] = 0
    damaged = control_graph(3)
    u, v = 0, damaged[0][0]
    damaged[u].remove(v)
    damaged[v].remove(u)
    assert not verify(damaged, 3)
    return {"status": "PASS", "controls": results, "degree57": estimate(57)}


if __name__ == "__main__":
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--estimate", type=int)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(), indent=2))
    else:
        print(json.dumps(estimate(args.estimate or 57), indent=2))
