#!/usr/bin/env python3
"""Zero-dependency independent witness verifier for Ramsey R(3,10) (n=40, triangle-free, alpha <= 9).

Verifies any candidate graph (40x40 binary adjacency matrix, graph6 string, edge-list JSON, or
edge-list text) using TWO independent exact algorithms:
  1. Exact Bron-Kerbosch with Tomita pivoting on the complement graph (exact alpha(G)).
  2. Exact bitmask branch-and-bound with greedy coloring upper bound (finds an explicit I_k
     counterexample or proves alpha(G) < k).

If ANY job ever reports a SAT witness for R(3,10), this verifier independently certifies
whether the graph is a genuine (3,10; 40)-Ramsey graph (implying R(3,10) = 41).
"""
import argparse
import hashlib
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Optional, Tuple


def _iter_bits(mask: int):
    while mask:
        b = mask & -mask
        yield b.bit_length() - 1
        mask ^= b


def decode_graph6(raw: str) -> List[int]:
    """Decode an ASCII graph6 string (n <= 62) into a bitmask adjacency list."""
    s = raw.strip()
    if s.startswith(">>graph6<<"):
        s = s[len(">>graph6<<"):]
    if not s:
        raise ValueError("Empty graph6 string")
    n = ord(s[0]) - 63
    if not (1 <= n <= 62):
        raise ValueError(f"Unsupported graph6 order n={n} (expected 1..62)")
    expected_len = 1 + (n * (n - 1) // 2 + 5) // 6
    if len(s) != expected_len:
        raise ValueError(f"Invalid graph6 length {len(s)} for n={n} (expected {expected_len})")
    if not all(63 <= ord(ch) <= 126 for ch in s):
        raise ValueError("Invalid non-printable character in graph6 string")
    adj = [0] * n
    k = 0
    for j in range(n):
        for i in range(j):
            if ((ord(s[1 + k // 6]) - 63) >> (5 - (k % 6))) & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return adj


def parse_adjacency_matrix_text(text: str) -> List[int]:
    """Parse a 0/1 adjacency matrix (rows of '0'/'1', optionally space-separated)."""
    lines = [ln.strip() for ln in text.splitlines() if ln.strip() and not ln.strip().startswith("#")]
    if not lines:
        raise ValueError("Empty adjacency matrix input")
    rows = []
    for ln in lines:
        toks = ln.split()
        if len(toks) == 1 and set(toks[0]) <= {"0", "1"}:
            row = [int(ch) for ch in toks[0]]
        elif all(t in ("0", "1") for t in toks):
            row = [int(t) for t in toks]
        else:
            raise ValueError(f"Invalid adjacency matrix row: {ln[:40]}")
        rows.append(row)
    n = len(rows)
    if any(len(r) != n for r in rows):
        raise ValueError(f"Non-square adjacency matrix: {n} rows with lengths {sorted(set(len(r) for r in rows))}")
    adj = [0] * n
    for i, row in enumerate(rows):
        mask = 0
        for j, val in enumerate(row):
            if val:
                mask |= 1 << j
        adj[i] = mask
    return adj


def load_graph(path: Path, fmt: str = "auto") -> List[int]:
    """Load a graph from file in adjacency matrix, graph6, or JSON edge-list format."""
    text = path.read_text(encoding="ascii").strip()
    if fmt == "graph6" or (fmt == "auto" and path.suffix == ".g6"):
        return decode_graph6(text.splitlines()[0])
    if fmt == "json" or (fmt == "auto" and path.suffix == ".json"):
        obj = json.loads(text)
        if "adj_bitmasks" in obj:
            return [int(x) for x in obj["adj_bitmasks"]]
        if "graph6" in obj:
            return decode_graph6(obj["graph6"])
        if "n" in obj and "edges" in obj:
            n = int(obj["n"])
            adj = [0] * n
            for u, v in obj["edges"]:
                u, v = int(u), int(v)
                if not (0 <= u < n and 0 <= v < n):
                    raise ValueError(f"Edge ({u}, {v}) out of range 0..{n-1}")
                adj[u] |= 1 << v
                adj[v] |= 1 << u
            return adj
        raise ValueError("Unsupported JSON graph schema (expected adj_bitmasks, graph6, or n+edges)")
    # Auto-detect single-line graph6 vs matrix
    lines = [ln.strip() for ln in text.splitlines() if ln.strip() and not ln.strip().startswith("#")]
    if fmt == "matrix" or len(lines) > 1 or set(lines[0]) <= {"0", "1", " "}:
        return parse_adjacency_matrix_text(text)
    return decode_graph6(lines[0])


def check_simple_undirected(adj: List[int]) -> Tuple[bool, Optional[str]]:
    """Verify no self-loops, no out-of-range bits, and strict symmetry."""
    n = len(adj)
    if n <= 0:
        return False, "Graph has 0 vertices"
    full = (1 << n) - 1
    for i in range(n):
        if adj[i] < 0 or (adj[i] & ~full) != 0:
            return False, f"Vertex {i} has out-of-range adjacency bits"
        if (adj[i] >> i) & 1:
            return False, f"Self-loop detected at vertex {i}"
    for i in range(n):
        for j in range(i + 1, n):
            ij = (adj[i] >> j) & 1
            ji = (adj[j] >> i) & 1
            if ij != ji:
                return False, f"Asymmetric edge between {i} and {j}: A[{i}][{j}]={ij}, A[{j}][{i}]={ji}"
    return True, None


def find_triangles(adj: List[int], limit: int = 1) -> Tuple[int, List[Tuple[int, int, int]]]:
    """Count triangles (or find first `limit` triangles) in exact bitmask arithmetic."""
    n = len(adj)
    found: List[Tuple[int, int, int]] = []
    total = 0
    for i in range(n):
        ni = adj[i] & ~((1 << (i + 1)) - 1)
        for j in _iter_bits(ni):
            common = ni & adj[j] & ~((1 << (j + 1)) - 1)
            if common:
                total += common.bit_count()
                if len(found) < limit:
                    for k in _iter_bits(common):
                        found.append((i, j, k))
                        if len(found) >= limit:
                            break
    return total, found


def exact_alpha_bron_kerbosch(adj: List[int]) -> Tuple[int, Tuple[int, ...], int]:
    """Algorithm A: Exact Bron-Kerbosch with Tomita pivoting on complement graph G_bar.

    Returns (alpha(G), witness_max_indep_set, maximal_independent_set_count).
    """
    n = len(adj)
    full = (1 << n) - 1
    # Complement adjacency: two distinct vertices are adjacent in G_bar iff nonadjacent in G
    comp = [full ^ ((1 << i) | adj[i]) for i in range(n)]
    best_size = 0
    best_mask = 0
    mis_count = 0

    def bk(r: int, r_sz: int, p: int, x: int):
        nonlocal best_size, best_mask, mis_count
        if p == 0 and x == 0:
            mis_count += 1
            if r_sz > best_size:
                best_size = r_sz
                best_mask = r
            return
        if p == 0:
            return
        # Tomita pivot maximizing |P & comp[u]|
        px = p | x
        pivot = -1
        pivot_deg = -1
        tmp = px
        while tmp:
            b = tmp & -tmp
            u = b.bit_length() - 1
            tmp ^= b
            d = (p & comp[u]).bit_count()
            if d > pivot_deg:
                pivot_deg = d
                pivot = u
        cands = p & ~comp[pivot]
        while cands:
            b = cands & -cands
            v = b.bit_length() - 1
            cands ^= b
            bk(r | b, r_sz + 1, p & comp[v], x & comp[v])
            p ^= b
            x |= b

    bk(0, 0, full, 0)
    return best_size, tuple(_iter_bits(best_mask)), mis_count


def _greedy_color_bound(cand: int, comp: List[int]) -> Tuple[List[int], List[int]]:
    """Order vertices in `cand` by greedy clique-cover/coloring in G_bar (upper bound on alpha)."""
    order: List[int] = []
    bounds: List[int] = []
    rem = cand
    color = 0
    while rem:
        color += 1
        # Independent set in G_bar = clique in G; since G is triangle-free, size <= 2,
        # but this works for ANY graph (triangle-free or not).
        avail = rem
        while avail:
            b = avail & -avail
            v = b.bit_length() - 1
            avail ^= b
            rem ^= b
            order.append(v)
            bounds.append(color)
            avail &= ~comp[v]
    return order, bounds


def find_indep_k_branch_and_bound(adj: List[int], k: int) -> Optional[Tuple[int, ...]]:
    """Algorithm B: Independent branch-and-bound with coloring upper bound for I_k existence.

    Returns an explicit k-vertex independent set if alpha(G) >= k, else None.
    """
    n = len(adj)
    if k <= 0:
        return ()
    if k > n:
        return None
    full = (1 << n) - 1
    comp = [full ^ ((1 << i) | adj[i]) for i in range(n)]

    def search(cand: int, need: int, cur: List[int]) -> Optional[Tuple[int, ...]]:
        if need == 0:
            return tuple(sorted(cur))
        if cand.bit_count() < need:
            return None
        order, bounds = _greedy_color_bound(cand, comp)
        # Iterate from back (highest color bound first)
        for idx in range(len(order) - 1, -1, -1):
            if bounds[idx] < need:
                return None
            v = order[idx]
            cand ^= (1 << v)
            cur.append(v)
            res = search(cand & comp[v], need - 1, cur)
            if res is not None:
                return res
            cur.pop()
        return None

    return search(full, k, [])


def canonical_matrix_sha256(adj: List[int]) -> str:
    n = len(adj)
    mat = "".join("".join("1" if (adj[i] >> j) & 1 else "0" for j in range(n)) + "\n" for i in range(n))
    return hashlib.sha256(mat.encode("ascii")).hexdigest()


def verify_ramsey_witness(adj: List[int], target_n: int = 40, forbidden_alpha: int = 10) -> Dict:
    """Independently verify whether `adj` is a (3, forbidden_alpha; target_n)-Ramsey graph."""
    t0 = time.monotonic()
    n = len(adj)
    result: Dict = {
        "target_n": target_n,
        "forbidden_alpha": forbidden_alpha,
        "n": n,
        "valid_witness": False,
        "verdict": "REJECTED",
        "reasons": [],
    }

    simple_ok, simple_err = check_simple_undirected(adj)
    result["simple_undirected"] = simple_ok
    if not simple_ok:
        result["reasons"].append(simple_err)
        result["elapsed_seconds"] = round(time.monotonic() - t0, 4)
        return result

    if n != target_n:
        result["reasons"].append(f"Vertex count mismatch: got n={n}, required n={target_n}")

    degs = [x.bit_count() for x in adj]
    edges = sum(degs) // 2
    deg_hist = {str(k): v for k, v in sorted(Counter(degs).items())}
    result["edges"] = edges
    result["min_degree"] = min(degs)
    result["max_degree"] = max(degs)
    result["degree_histogram"] = deg_hist
    result["matrix_sha256"] = canonical_matrix_sha256(adj)

    tri_count, first_tris = find_triangles(adj, limit=5)
    result["triangle_count"] = tri_count
    result["triangle_free"] = (tri_count == 0)
    if tri_count > 0:
        result["first_triangle"] = list(first_tris[0])
        result["reasons"].append(f"Graph contains {tri_count} triangle(s), e.g. {list(first_tris[0])}")

    # Independent exact independence number check (Algorithms A and B)
    alpha_bk, witness_max_iset, mis_count = exact_alpha_bron_kerbosch(adj)
    bnb_ik = find_indep_k_branch_and_bound(adj, forbidden_alpha)

    # Cross-check consistency between Algorithm A and Algorithm B
    if (alpha_bk >= forbidden_alpha) != (bnb_ik is not None):
        raise RuntimeError(
            f"INTERNAL VERIFIER DISAGREEMENT: Bron-Kerbosch alpha={alpha_bk}, "
            f"Branch-and-Bound I_{forbidden_alpha}={bnb_ik}"
        )

    # Independently verify the returned independent set actually has 0 internal edges
    for u in witness_max_iset:
        for v in witness_max_iset:
            if u != v and ((adj[u] >> v) & 1):
                raise RuntimeError(f"INTERNAL ERROR: max independent set has edge ({u},{v})")
    if bnb_ik is not None:
        assert len(bnb_ik) == forbidden_alpha and len(set(bnb_ik)) == forbidden_alpha
        for u in bnb_ik:
            for v in bnb_ik:
                if u != v and ((adj[u] >> v) & 1):
                    raise RuntimeError(f"INTERNAL ERROR: B&B I_k has edge ({u},{v})")

    result["alpha"] = alpha_bk
    result["maximal_independent_sets"] = mis_count
    result["max_independent_set_example"] = list(witness_max_iset)
    result["cross_check_consistent"] = True
    if bnb_ik is not None:
        result["forbidden_independent_set_example"] = list(bnb_ik)
        result["reasons"].append(
            f"Independence number alpha(G)={alpha_bk} >= {forbidden_alpha} "
            f"(explicit I_{forbidden_alpha}: {list(bnb_ik)})"
        )

    if not result["reasons"]:
        result["valid_witness"] = True
        result["verdict"] = (
            "VERIFIED_RAMSEY_R310_WITNESS"
            if (target_n == 40 and forbidden_alpha == 10)
            else f"VERIFIED_RAMSEY_3_{forbidden_alpha}_{target_n}_WITNESS"
        )
    result["elapsed_seconds"] = round(time.monotonic() - t0, 4)
    return result


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Zero-dependency independent Ramsey R(3,10) 40-vertex witness verifier."
    )
    ap.add_argument("input_file", type=Path, help="Graph file (40x40 matrix .txt, .g6, or .json)")
    ap.add_argument("--format", choices=["auto", "matrix", "graph6", "json"], default="auto")
    ap.add_argument("--n", type=int, default=40, help="Required vertex count (default: 40)")
    ap.add_argument("--k", type=int, default=10, help="Forbidden independent set size (default: 10, i.e. alpha <= 9)")
    ap.add_argument("--out", type=Path, default=None, help="Optional JSON output path")
    args = ap.parse_args()

    adj = load_graph(args.input_file, fmt=args.format)
    report = verify_ramsey_witness(adj, target_n=args.n, forbidden_alpha=args.k)
    text = json.dumps(report, indent=2) + "\n"
    if args.out is not None:
        args.out.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0 if report["valid_witness"] else 1


if __name__ == "__main__":
    sys.exit(main())
