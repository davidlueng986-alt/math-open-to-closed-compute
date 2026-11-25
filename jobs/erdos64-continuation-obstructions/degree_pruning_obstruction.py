"""Prescribed 13-vertex obstruction to a degree/pruning upgrade.

NOT an Erdos-Gyarfas counterexample: this graph contains power cycles.
No search/census. Builds one graph and supplies replayable certificates
excluding every possible induced Near subgraph.
"""
import json
from pathlib import Path


def build():
    vertices = set(range(14))
    edges = {tuple(sorted((i, 7+j)))
             for j in range(7) for i in ((j+d) % 7 for d in (0,1,3))}
    assert len(edges) == 21
    edges.remove((0,7))
    contract = lambda x: 2 if x == 8 else x
    edges = {tuple(sorted((contract(a), contract(b)))) for a,b in edges
             if contract(a) != contract(b)}
    vertices.remove(8)
    graph = {v: set() for v in vertices}
    for a,b in edges:
        graph[a].add(b)
        graph[b].add(a)
    return graph


def cycle_lengths(graph):
    witnesses = {}
    for start in graph:
        def walk(v, path, visited):
            for u in graph[v]:
                if u == start and len(path) >= 3 and path[1] < path[-1]:
                    witnesses.setdefault(len(path), path[:])
                elif u > start and u not in visited:
                    walk(u, path+[u], visited | {u})
        walk(start, [start], {start})
    return witnesses


def near_core_certificate(graph, root):
    alive = set(graph)
    removals = []
    while True:
        bad = sorted(v for v in alive if v != root and len(graph[v] & alive) < 3)
        if not bad:
            break
        v = bad[0]
        removals.append({"vertex": v, "current_degree": len(graph[v] & alive)})
        alive.remove(v)
    return {"exception": root, "removals": removals,
            "survivors": sorted(alive),
            "surviving_degrees": {str(v): len(graph[v] & alive) for v in sorted(alive)}}


def replay(graph, certificate):
    root = certificate["exception"]
    alive = set(graph)
    for record in certificate["removals"]:
        v = record["vertex"]
        assert v in alive and v != root
        degree = sum(u in alive for u in graph[v])
        assert degree == record["current_degree"] and degree < 3
        alive.remove(v)
    assert sorted(alive) == certificate["survivors"]
    assert not any(len(graph[v] & alive) >= 3 for v in alive)
    # A Near induced subgraph with designated exception root would survive
    # every removal and would retain a vertex of degree >=3 at the end.
    return True


def main():
    graph = build()
    known_edges = [(0,11),(0,13),(1,2),(1,7),(1,12),(2,4),(2,9),(2,13),
                   (3,7),(3,9),(3,10),(4,10),(4,11),(5,9),(5,11),(5,12),
                   (6,10),(6,12),(6,13)]
    assert sorted((a,b) for a in graph for b in graph[a] if a < b) == known_edges
    assert {v for v in graph if len(graph[v]) == 2} == {0,7}
    assert {v for v in graph if len(graph[v]) == 4} == {2}
    assert all(len(graph[v]) == 3 for v in graph if v not in {0,7,2})
    cycles = cycle_lengths(graph)
    assert 4 not in cycles
    powers = sorted(n for n in cycles if n >= 4 and n & (n-1) == 0)
    assert powers  # Scope check: do not accidentally label original counterexample.
    certificates = [near_core_certificate(graph, w) for w in sorted(graph)]
    assert all(replay(graph, cert) for cert in certificates)
    result = {
        "purpose": "Refutes internal-high-degree implies Near-subgraph under C4-free degree conditions",
        "original_counterexample": False,
        "near": False,
        "order": len(graph), "size": len(known_edges),
        "degree_counts": {str(d): sum(len(adj)==d for adj in graph.values()) for d in [2,3,4]},
        "ports": [0,7], "high_vertex": 2, "c4_free": True,
        "cycle_lengths": sorted(cycles), "power_cycle_lengths": powers,
        "power_cycle_witnesses": {str(n): cycles[n] for n in powers},
        "no_induced_near_subgraph": True,
        "certificates": certificates,
        "adjacency": {str(v): sorted(adj) for v,adj in graph.items()}
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k not in {"certificates","adjacency"}}, indent=2))


if __name__ == "__main__":
    main()

