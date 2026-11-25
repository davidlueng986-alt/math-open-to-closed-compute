"""One explicit construction refuting a two-cut spectrum-only inference.

This is NOT an Erdos-Gyarfas counterexample: its minimum degree is 2.
No graph search or census is performed. All cycles and terminal paths of
one prescribed graph are independently enumerated to audit the formulas.
"""
import json
from pathlib import Path


def multitheta(lengths, terminal_positions):
    graph = {0: set(), 1: set()}
    paths = []
    fresh = 2
    for length in lengths:
        path = [0]
        for _ in range(length - 1):
            graph[fresh] = set()
            path.append(fresh)
            fresh += 1
        path.append(1)
        for a, b in zip(path, path[1:]):
            graph[a].add(b)
            graph[b].add(a)
        paths.append(path)
    p, q = terminal_positions
    return graph, (paths[0][p], paths[0][q])


def simple_paths(graph, a, b):
    lengths = []
    def go(x, used, length):
        if x == b:
            lengths.append(length)
            return
        for y in graph[x] - used:
            go(y, used | {y}, length + 1)
    go(a, {a}, 0)
    return sorted(lengths)


def simple_cycles(graph):
    cycles = []
    for start in graph:
        def go(x, path, used):
            for y in graph[x]:
                if y == start and len(path) >= 3:
                    if path[1] < path[-1]:
                        cycles.append(tuple(path))
                elif y > start and y not in used:
                    go(y, path + [y], used | {y})
        go(start, [start], {start})
    return cycles


def is_power(n):
    return n >= 4 and n & (n - 1) == 0


def connected_after_removal(graph, removed=None):
    remaining = set(graph) - {removed}
    if not remaining:
        return True
    seen, todo = set(), [min(remaining)]
    while todo:
        v = todo.pop()
        if v in seen:
            continue
        seen.add(v)
        todo.extend((graph[v] & remaining) - seen)
    return seen == remaining


def main():
    left, (a0, a1) = multitheta([4, 1, 2], [1, 3])
    right, (b0, b1) = multitheta([10, 11, 12, 13], [1, 9])
    offset = len(left)
    graph = {v: set(adj) for v, adj in left.items()}
    graph.update({v+offset: {w+offset for w in adj}
                  for v, adj in right.items()})
    for a, b in [(a0, b0+offset), (a1, b1+offset)]:
        graph[a].add(b)
        graph[b].add(a)
    pa = simple_paths(left, a0, a1)
    pb = simple_paths(right, b0, b1)
    cycles = simple_cycles(graph)
    internal_a = sorted(len(c) for c in simple_cycles(left))
    internal_b = sorted(len(c) for c in simple_cycles(right))
    crossing = sorted(p+q+2 for p in pa for q in pb)
    assert pa == [2, 3, 4]
    assert pb == [8, 13, 14, 15]
    assert sorted(map(len, cycles)) == sorted(internal_a + internal_b + crossing)
    assert len(graph) == 50 and len(cycles) == 21
    assert not any(is_power(len(c)) for c in cycles)
    assert all(connected_after_removal(graph, v) for v in graph)
    sums = sorted({p+q for p in pa for q in pb})
    assert 15 in sums and 16 in sums and 14 not in sums
    assert 4 in {p+1 for p in pa} and 16 in {p+1 for p in pb}
    assert 4 in {p+2 for p in pa} and 16 in {p+2 for p in pb}
    assert 4 in pa and 8 in pb
    assert 16 in {s+1 for s in sums} and 16 in sums
    assert 8 in {p+q+2 for p in pa for q in pa}
    assert 32 in {p+q+2 for p in pb for q in pb}
    result = {
        "purpose": "Explicit obstruction to spectrum-only inference; NOT original counterexample",
        "order": len(graph),
        "edge_count": sum(map(len, graph.values())) // 2,
        "degree_counts": {str(d): sum(len(adj)==d for adj in graph.values()) for d in [2,3,4]},
        "near": False,
        "biconnected": True,
        "left_ports": [a0,a1], "right_ports": [b0+offset,b1+offset],
        "left_spectrum": pa, "right_spectrum": pb,
        "internal_left_cycles": internal_a,
        "internal_right_cycles": internal_b,
        "crossing_cycles": crossing,
        "all_cycle_lengths": sorted(set(map(len, cycles))),
        "total_simple_cycles": len(cycles),
        "no_power_cycles": True,
        "edge_close_power_witnesses": [4,16],
        "two_edge_path_close_power_witnesses": [4,16],
        "port_identification_power_witnesses": [4,8],
        "one_cut_edge_contraction_power_witness": 16,
        "both_cut_edge_contraction_power_witness": 16,
        "self_gluing_power_witnesses": [8,32],
        "adjacency": {str(v):sorted(adj) for v,adj in graph.items()},
    }
    dest = Path(__file__).with_name("obstruction.json")
    dest.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "adjacency"},indent=2))


if __name__ == "__main__":
    main()
