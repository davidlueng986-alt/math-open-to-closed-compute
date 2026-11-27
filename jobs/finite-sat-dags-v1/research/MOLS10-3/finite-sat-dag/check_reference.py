"""Independent small-order semantic controls for the reference MOLS CNF.

Run from any directory. Enumerates all Latin families at the tested tiny orders,
compares CNF projection against direct original-space orthogonality, then checks
the independent order-four witness and the exact order-ten generation counts.
This is an implementation control, not an order-ten solution or proof replay.
"""

import itertools
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from finite_sat import mols


class Builder:
    def __init__(self):
        self.mapping = {}
        self.clauses = []

    def var(self, key):
        if key not in self.mapping:
            self.mapping[key] = len(self.mapping) + 1
        return self.mapping[key]

    def add(self, clause):
        self.clauses.append(tuple(clause))


def latin_squares(n):
    permutations = list(itertools.permutations(range(n)))
    return [list(map(list, rows)) for rows in itertools.product(permutations, repeat=n)
            if all(len({row[c] for row in rows}) == n for c in range(n))]


def orthogonal(family):
    n = len(family[0])
    return all(len({(a[r][c], b[r][c]) for r in range(n) for c in range(n)}) == n*n
               for a, b in itertools.combinations(family, 2))


def evaluate(builder, family):
    truth = set()
    for key, variable in builder.mapping.items():
        if key[0] == "x":
            _, t, r, c, s = key
            value = family[t][r][c] == s
        else:
            _, a, b, r, u, v = key
            c = family[a][r].index(u)
            value = family[b][r][c] == v
        truth.add(variable if value else -variable)
    return all(any(v in truth for v in clause) for clause in builder.clauses)


def main():
    results = []
    for n, k in [(2, 1), (2, 2), (3, 2), (3, 3)]:
        builder = Builder()
        meta = mols.emit(builder, n, k, normalize=False)
        assert len(builder.mapping) == meta["expected_variables"]
        assert len(builder.clauses) == meta["expected_clauses"]
        options = latin_squares(n)
        total = sat = 0
        for family in itertools.product(options, repeat=k):
            expected = orthogonal(family)
            actual = evaluate(builder, family)
            assert expected == actual, (n, k, family)
            total += 1
            sat += actual
            if actual:
                normalized = mols.normalize(family)
                nb = Builder()
                nm = mols.emit(nb, n, k)
                assignment = mols.witness_assignment(normalized, nb)
                assert evaluate(nb, normalized)
                assert mols.decode(assignment, nm) == normalized
        results.append({"n": n, "k": k, "latin_families_exhausted": total,
                        "orthogonal_families": sat, "semantic_projection": "PASS"})
    gf4 = [
        [[0, 1, 2, 3], [1, 0, 3, 2], [2, 3, 0, 1], [3, 2, 1, 0]],
        [[0, 1, 2, 3], [2, 3, 0, 1], [3, 2, 1, 0], [1, 0, 3, 2]],
        [[0, 1, 2, 3], [3, 2, 1, 0], [1, 0, 3, 2], [2, 3, 0, 1]],
    ]
    builder = Builder()
    meta = mols.emit(builder, 4, 3)
    assignment = mols.witness_assignment(gf4, builder)
    assert mols.verify(gf4, 4, 3)["valid"]
    assert evaluate(builder, gf4)
    assert mols.decode(assignment, meta) == gf4
    results.append({"n": 4, "k": 3, "independent_GF4_witness": "PASS",
                    "variables": len(builder.mapping), "clauses": len(builder.clauses)})
    builder = Builder()
    mols.emit(builder, 10, 3)
    assert len(builder.mapping) == 6000 and len(builder.clauses) == 112839
    split = [builder.var(t) for t in [("x", 0, 1, 1, 2), ("x", 0, 1, 2, 3),
                                    ("x", 1, 1, 0, 2), ("x", 2, 1, 0, 3)]]
    assert split == [113, 124, 1103, 2104]
    results.append({"n": 10, "k": 3, "generation_only": "PASS",
                    "variables": len(builder.mapping), "clauses": len(builder.clauses),
                    "split_variables": split, "solved": False})
    print(json.dumps({"status": "PASS",
                      "scope": "Reference CNF semantic controls and exact generation counts; no order-ten search or negative proof",
                      "checks": results}, indent=2))


if __name__ == "__main__":
    main()
