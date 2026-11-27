"""Independent positive control for every Moore reference clause family.

Construct a 50-vertex degree-7 graph directly, then derive a rooted normalized
assignment rather than relying on the CNF generator to construct the graph.
This is a semantic regression control, not degree-57 evidence.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
from finite_sat import moore
from finite_sat.core import MemoryCNF


def run():
    k = 7
    adjacency = [set() for _ in range(50)]

    def link(u, v):
        adjacency[u].add(v)
        adjacency[v].add(u)

    def p(i, j):
        return 5 * i + j % 5

    def q(i, j):
        return 25 + 5 * i + j % 5

    # Five pentagons P, five pentagrams Q, and bilinear matchings over F_5.
    for i in range(5):
        for j in range(5):
            link(p(i, j), p(i, j + 1))
            link(q(i, j), q(i, j + 2))
            for h in range(5):
                link(p(i, j), q(h, i * h + j))
    assert moore.verify([sorted(row) for row in adjacency], k)

    # Extract the rooted representation from the preexisting graph.
    parents = sorted(adjacency[0])
    groups = [sorted(adjacency[u] - {0}) for u in parents]
    assert len(parents) == k
    assert all(len(group) == k - 1 for group in groups)
    assert len({v for group in groups for v in group}) == k * (k - 1)
    for j in range(1, k):
        old = set(groups[j])
        matches = [adjacency[u] & old for u in groups[0]]
        assert all(len(match) == 1 for match in matches)
        groups[j] = [next(iter(match)) for match in matches]
        assert len(set(groups[j])) == k - 1

    builder = MemoryCNF()
    metadata = moore.emit(builder, k)
    assignment = []
    for key, variable in builder.variables.items():
        _, i, j, a, b = key
        present = groups[j][b] in adjacency[groups[i][a]]
        assignment.append(variable if present else -variable)
    assert builder.nvars == metadata["primary_variables"] == 540
    assert builder.nclauses == metadata["clauses"] == 67770
    assert builder.satisfied(assignment)
    decoded = moore.decode(builder, assignment, k)
    assert moore.verify(decoded, k)
    return {
        "status": "PASS",
        "scope": "degree-7 semantic positive control; no degree-57 result",
        "construction": "five pentagons and five pentagrams with bilinear F5 matchings",
        "vertices": 50,
        "degree": k,
        "variables": builder.nvars,
        "clauses": builder.nclauses,
        "independent_original_graph_check": True,
        "rooted_normalization_check": True,
        "all_clause_families_satisfied": True,
        "decoded_original_graph_check": True,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
