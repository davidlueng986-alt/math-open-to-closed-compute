#!/usr/bin/env python3
"""Finite checks supporting (not proving) the all-order gadget argument.

No external libraries. Prints exact port spectra and an explicit obstruction
to inferring a dyadic cycle from an arbitrary perfect-matching alternating
cycle. The infinite theorem itself is in alternating-extension.md.
"""

import json
from pathlib import Path


EDGES = [(0, 1), (0, 2), (1, 4), (2, 3), (3, 4), (3, 5), (4, 5)]


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        assert a != b
        assert b not in adj[a]
        adj[a].add(b)
        adj[b].add(a)
    return adj


def simple_paths(adj, source, target):
    out = []
    path = [source]
    seen = {source}

    def rec(v):
        if v == target:
            out.append(path.copy())
            return
        for w in sorted(adj[v] - seen):
            seen.add(w)
            path.append(w)
            rec(w)
            path.pop()
            seen.remove(w)

    rec(source)
    return out


def cycle_of_length(adj, length):
    """Return a simple undirected witness, enumerating least vertex first."""
    for source in range(len(adj)):
        path = [source]
        seen = {source}

        def rec(v):
            if len(path) == length:
                if source in adj[v]:
                    return path.copy()
                return None
            for w in sorted(adj[v]):
                if w <= source or w in seen:
                    continue
                path.append(w)
                seen.add(w)
                ans = rec(w)
                if ans:
                    return ans
                seen.remove(w)
                path.pop()
            return None

        ans = rec(source)
        if ans:
            return ans
    return None


def verify_cycle(adj, path, expected_length):
    assert len(path) == expected_length
    assert len(set(path)) == expected_length
    assert all(path[(i + 1) % expected_length] in adj[v]
               for i, v in enumerate(path))


def directed_cycle_lengths(adj):
    lengths = set()
    for source in range(len(adj)):
        seen = {source}

        def rec(v, length):
            for w in adj[v]:
                if w == source:
                    lengths.add(length)
                elif w > source and w not in seen:
                    seen.add(w)
                    rec(w, length + 1)
                    seen.remove(w)

        rec(source, 1)
    return sorted(lengths)


def cyclic_tripartite_example(s):
    """R_ij--B_ij in M; R_ij--B_(i+1),j and B_(i+1),(j+1) in F."""
    assert s >= 3

    def vid(i, j, side):
        return 2 * (s * (i % 3) + (j % s)) + side

    edges = []
    matching = []
    digraph = [set() for _ in range(3 * s)]
    for i in range(3):
        for j in range(s):
            matching.append((vid(i, j, 0), vid(i, j, 1)))
            for delta in (0, 1):
                edges.append((vid(i, j, 0), vid(i + 1, j + delta, 1)))
                digraph[s * i + j].add(s * ((i + 1) % 3) + (j + delta) % s)
    edges += matching
    adj = adjacency(6 * s, edges)
    assert all(len(v) == 3 for v in adj)
    assert all(a % 2 != b % 2 for a, b in edges)
    directed = directed_cycle_lengths(digraph)
    assert all(x % 3 == 0 for x in directed)
    alternating = [2 * x for x in directed]
    assert all(x & (x - 1) for x in alternating)
    powers = {}
    p = 4
    while p <= 6 * s:
        powers[str(p)] = cycle_of_length(adj, p)
        if powers[str(p)] is not None:
            verify_cycle(adj, powers[str(p)], p)
        p *= 2
    if s == 3:
        assert alternating == [6, 12, 18]
        assert powers["4"] is None
        assert powers["8"] is not None
        assert powers["16"] is not None
    return {
        "s": s,
        "order": len(adj),
        "simple": True,
        "cubic": True,
        "bipartite_partition": "even vertex labels R; odd vertex labels B",
        "label_encoding": "vertex 2*(s*i+j)+side; side 0=R,1=B; i modulo 3,j modulo s",
        "edges": edges,
        "matching": matching,
        "M_alternating_cycle_lengths": alternating,
        "power_cycle_witnesses": powers,
    }


def main():
    adj = adjacency(6, EDGES)
    spectra = {}
    for a, b in [(0, 1), (0, 2), (5, 1), (5, 2), (0, 5), (1, 2)]:
        paths = simple_paths(adj, a, b)
        spectra[f"{a}-{b}"] = {
            "lengths": sorted({len(p) - 1 for p in paths}),
            "one_witness_per_length": {
                str(len(p) - 1): p for p in paths
            },
        }
    assert spectra["0-1"]["lengths"] == [1, 4, 5]
    assert spectra["0-2"]["lengths"] == [1, 4, 5]
    assert spectra["5-1"]["lengths"] == [2, 3, 4, 5]
    assert spectra["5-2"]["lengths"] == [2, 3, 4, 5]
    assert spectra["0-5"]["lengths"] == [3, 4]
    assert spectra["1-2"]["lengths"] == [2, 3, 4]

    # Sanity check the closed-form all-A construction, all block counts <= 4096.
    for m in range(2, 4097):
        power = 1 << (2 * m - 1).bit_length()
        if power == 2 * m + 2:
            power *= 2
        delta = power - 2 * m
        if delta % 4 == 0:
            a, b = 0, delta // 4
        else:
            assert delta >= 6 and delta % 4 == 2
            a, b = 2, (delta - 6) // 4
        assert a >= 0 and b >= 0 and a + b <= m
        assert 2 * m + 3 * a + 4 * b == power

    # Direct finite sumset check, deliberately separate from the infinite proof.
    for m in range(2, 65):
        for q in range(m + 1):
            vals = {m}
            for i in range(m):
                spectrum = [2, 3, 4, 5] if i < q else [1, 4, 5]
                vals = {x + y for x in vals for y in spectrum}
            if q:
                assert vals == set(range(2 * m + q, 6 * m + 1))
            assert any(x >= 4 and x & (x - 1) == 0 for x in vals)

    result = {
        "status": "finite_audit_passed; ordinary_all_order_proof_only; no_Lean_or_DAG_closure_claim",
        "purpose": "Independent finite path/arithmetic audit, not a global proof",
        "gadget_edges": EDGES,
        "port_spectra": spectra,
        "bounded_arithmetic_regression_only": {
            "all_A_closed_form_checked_m": [2, 4096],
            "all_mixed_sumsets_checked_m": [2, 64],
        },
        "arbitrary_assembly_ordinary_proof_dependency": {
            "theorem": "Grossman-Haggkvist regular-subgraphs alternating-cycle corollary",
            "doi": "10.1016/0095-8956(83)90008-4",
            "Lean_verified_here": False,
            "assembly_enumeration_claimed": False,
        },
        "obstruction_mod3_proof": "Every M-alternating simple cycle projects to a directed simple cycle on (i,j) whose arcs increase i modulo 3. Hence its original length is divisible by 6 and cannot be a power of two. This holds for every s>=3, independently of finite enumeration.",
        "alternating_cycle_obstructions": [cyclic_tripartite_example(3)],
    }
    path = Path(__file__).with_name("audit.json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "output": str(path),
        "spectra": {k: v["lengths"] for k, v in spectra.items()},
        "obstructions": [{"order": r["order"], "M_alternating_cycle_lengths": r["M_alternating_cycle_lengths"], "power_cycles": {k: v is not None for k, v in r["power_cycle_witnesses"].items()}} for r in result["alternating_cycle_obstructions"]],
    }, indent=2))


if __name__ == "__main__":
    main()
