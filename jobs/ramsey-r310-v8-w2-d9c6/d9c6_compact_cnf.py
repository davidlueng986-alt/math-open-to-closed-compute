#!/usr/bin/env python3
r"""V8 Production Compact 312-variable D9-C6 DIMACS CNF encoder, verifier, and proof-first Kissat/DRAT/LRAT solver.

Mathematical specification for D9-C6 (9-regular triangle-free 40-vertex graph with alpha(G) <= 9
and global maximum non-edge codegree c = 6):
  - Roots 0, 1 are nonadjacent with |N(0) & N(1)| = 6.
  - S = N(0) & N(1) (|S| = 6, vertices 2..7),
    X = N(0) \ N(1) (|X| = 3, vertices 8..10),
    Y = N(1) \ N(0) (|Y| = 3, vertices 11..13),
    T = V \ ({0,1} U S U X U Y) (|T| = 26, vertices 14..39).
  - A = N(0) = S U X (|A| = 9, independent), B = N(1) = S U Y (|B| = 9, independent).
  - The induced bipartite skeleton H = G[X, Y] has e_XY = e(X, Y) edges.
  - Degree counting gives e(T) = 72 + e_XY. Since alpha(T) <= 7 (else I_8 U {0,1} is I_10)
    and e(3, 8, 26) = 73 (Goedgebeur & Radziszowski 2013), 1 <= e_XY <= 9 and 73 <= e(T) <= 81.
  - Under S_3(X) x S_3(Y) x Z_2(X <-> Y) (order 72), all 2^9 - 1 = 511 nonempty 3x3 skeletons
    collapse to exactly 25 canonical orbits D9-C6-S00 .. D9-C6-S24.
  - For a fixed (3, 8; 26) core T and canonical orbit H with e(T) = 72 + e_XY, only the
    12 x 26 = 312 edge variables M[r][t] (r in S+X+Y, t in T) remain unfixed.

Every encoded constraint is a proved necessary condition (zero heuristic pruning):
  1. Triangle-free with T: 12 * e(T) binary clauses.
  2. Triangle-free with H = G[X, Y]: 26 * e_XY binary clauses (for e_XY=9, forces U_X & U_Y = empty).
  3. Exact row degrees: deg_T(s) = 7 (s in S), deg_T(x) = 8 - d_Y(x), deg_T(y) = 8 - d_X(y).
  4. Exact column degrees + A/B codegree & domination bounds + generalized S-domination:
       sum_{r=0..11} M[r][t] = rem[t] = 9 - d_T(t),
       1 <= d_A(t) <= 6,  1 <= d_B(t) <= 6,
       d_S(t) >= max(1 if rem[t] > alpha_both(H) else 0, rem[t] - alpha(H)).
  5. Exact saturation (non-edge codegree >= 1, since N(v) is an I_9 for every v):
       - S -> T: M[s][t] OR OR_{u in N_T(t)} M[s][u]
       - X -> T: M[x][t] OR OR_{y in N_Y(x)} M[y][t] OR OR_{u in N_T(t)} M[x][u]
       - Y -> T: M[y][t] OR OR_{x in N_X(y)} M[x][t] OR OR_{u in N_T(t)} M[y][u]
       - Nonadjacent (x, y) not in E(H): |N_T(x) & N_T(y)| >= 1
       - Nonadjacent (u, v) in T with codeg_T(u, v) == 0: |N_{S+X+Y}(u) & N_{S+X+Y}(v)| >= 1
  6. Exact pairwise non-edge codegree caps (<= 6):
       - (s1, s2): <= 4
       - (s, x), (s, y): <= 5 (emitted only when nontrivial, i.e., deg_T(x/y) >= 6)
       - (x1, x2): <= 5 - |N_Y(x1) & N_Y(x2)| (emitted only when nontrivial)
       - (y1, y2): <= 5 - |N_X(y1) & N_X(y2)| (emitted only when nontrivial)
       - Nonadjacent (x, y) not in E(H): <= 6 (emitted only when min(deg_T(x), deg_T(y)) > 6)
       - Nonadjacent (u, v) in T: <= 6 - codeg_T(u, v) ONLY when min(rem[u], rem[v]) > 6 - codeg_T(u, v)
         (zero redundant T-pair counters!).
  7. Exact Hall b=1 private-neighbor caps: for every r in A (resp. B), at most 1 vertex t in T
     has N_A(t) = {r} (resp. N_B(t) = {r}).
  8. Optional Hall b=2 bounds: for every pair {r1, r2} in A (resp. B), at most 3 vertices t in T
     have N_A(t) subset {r1, r2} (proved via Hall b=1 + alpha <= 2 on U).
  9. Optional static I_7(T) hitting-set constraints: for every W in I_7(T), at most 2 rows of A
     and at most 2 rows of B may miss W.
 10. Sound automorphism-respecting symmetry breaking:
       - Strict lex on S: M[0] < M[1] < M[2] < M[3] < M[4] < M[5] (strict since cap=4 < deg=7).
       - Strict lex within each twin class of X (same N_Y) and each twin class of Y (same N_X)
         (strict since cap = 5 - d_Y < 8 - d_Y = deg_T).
       - Non-strict lex M[6] <= M[9] whenever the canonical skeleton H is transpose-symmetric
         (adj_x == adj_y), which preserves all twin-class orderings under X <-> Y swap.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import itertools
import json
import os
import resource
import shutil
import subprocess
import time
from pathlib import Path

N_T = 26
N_G = 40
NUM_S = 6
NUM_X = 3
NUM_Y = 3
NUM_ROWS = NUM_S + NUM_X + NUM_Y  # 12
NUM_PRIMARY_VARS = NUM_ROWS * N_T  # 312
G6_LEN_26 = 1 + (N_T * (N_T - 1) // 2 + 5) // 6  # 56

PERMS_3 = list(itertools.permutations(range(3)))


def canon_3x3(mask: int) -> int:
    """Canonical representative of a 3x3 bipartite graph under S_3(X) x S_3(Y) x Z_2."""
    best = 1 << 9
    for px in PERMS_3:
        for py in PERMS_3:
            for sw in (0, 1):
                m = 0
                for i in range(3):
                    for j in range(3):
                        if (mask >> (3 * i + j)) & 1:
                            ni, nj = (py[j], px[i]) if sw else (px[i], py[j])
                            m |= 1 << (3 * ni + nj)
                if m < best:
                    best = m
    return best


def _skeleton_invariants(mask: int) -> dict:
    adj_x = [(mask >> (3 * i)) & 7 for i in range(3)]
    adj_y = [sum((((mask >> (3 * i + j)) & 1) << i) for i in range(3)) for j in range(3)]

    alpha_h = 0
    alpha_both_h = 0
    max_min_ab = 0
    for xm in range(8):
        # Vertices in Y forbidden by edges from xm
        forb_y = 0
        for i in range(3):
            if (xm >> i) & 1:
                forb_y |= adj_x[i]
        for ym in range(8):
            if ym & forb_y:
                continue
            a = xm.bit_count()
            b = ym.bit_count()
            sz = a + b
            if sz > alpha_h:
                alpha_h = sz
            if a > 0 and b > 0:
                if sz > alpha_both_h:
                    alpha_both_h = sz
                if min(a, b) > max_min_ab:
                    max_min_ab = min(a, b)

    max_rem_t = min(9, 6 + max_min_ab)
    min_deg_t = max(3, 9 - max_rem_t)

    # Twin classes (identical neighborhood in opposite part)
    twins_x_map: dict[int, list[int]] = {}
    for i, m in enumerate(adj_x):
        twins_x_map.setdefault(m, []).append(i)
    twins_y_map: dict[int, list[int]] = {}
    for j, m in enumerate(adj_y):
        twins_y_map.setdefault(m, []).append(j)

    twin_classes_x = [cls for cls in twins_x_map.values() if len(cls) >= 2]
    twin_classes_y = [cls for cls in twins_y_map.values() if len(cls) >= 2]
    transpose_symmetric = (adj_x == adj_y)

    return {
        "adj_x": adj_x,
        "adj_y": adj_y,
        "deg_T_X": [8 - m.bit_count() for m in adj_x],
        "deg_T_Y": [8 - m.bit_count() for m in adj_y],
        "cap_T_XX": {
            f"{i},{j}": 5 - (adj_x[i] & adj_x[j]).bit_count()
            for i in range(3) for j in range(i + 1, 3)
        },
        "cap_T_YY": {
            f"{i},{j}": 5 - (adj_y[i] & adj_y[j]).bit_count()
            for i in range(3) for j in range(i + 1, 3)
        },
        "alpha_H": alpha_h,
        "alpha_both_H": alpha_both_h,
        "max_rem_T": max_rem_t,
        "min_deg_T": min_deg_t,
        "twin_classes_X": twin_classes_x,
        "twin_classes_Y": twin_classes_y,
        "transpose_symmetric": transpose_symmetric,
        "forces_full_S_domination": (mask.bit_count() == 9),
    }


def enumerate_d9c6_skeletons() -> list[dict]:
    """Return all 25 canonical D9-C6 3x3 bipartite skeleton orbits covering all 511 nonempty graphs."""
    orbits: dict[int, int] = {}
    for mask in range(1, 1 << 9):
        c = canon_3x3(mask)
        orbits[c] = orbits.get(c, 0) + 1
    assert sum(orbits.values()) == 511, f"Expected 511 skeletons, got {sum(orbits.values())}"
    assert len(orbits) == 25, f"Expected 25 canonical orbits, got {len(orbits)}"

    records = []
    for idx, (mask, size) in enumerate(sorted(orbits.items(), key=lambda kv: (kv[0].bit_count(), kv[0]))):
        e_xy = mask.bit_count()
        rec = {
            "id": f"D9-C6-S{idx:02d}",
            "orbit_idx": idx,
            "mask": mask,
            "e_xy": e_xy,
            "e_T": 72 + e_xy,
            "orbit_size": size,
        }
        rec.update(_skeleton_invariants(mask))
        records.append(rec)
    return records


def decode_g6(raw: str, expected_n: int = N_T) -> list[int]:
    """Decode a graph6 string into a bitmask adjacency list."""
    s = raw.strip().removeprefix(">>graph6<<")
    n = ord(s[0]) - 63
    exp_len = 1 + (n * (n - 1) // 2 + 5) // 6
    assert n == expected_n and len(s) == exp_len, f"Bad graph6 (n={n}, len={len(s)}): {s[:20]}"
    adj = [0] * n
    k = 0
    for j in range(n):
        for i in range(j):
            if ((ord(s[1 + k // 6]) - 63) >> (5 - k % 6)) & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return adj


def encode_g6(adj: list[int]) -> str:
    """Encode a bitmask adjacency list (n <= 62) into canonical graph6 ASCII."""
    n = len(adj)
    assert 1 <= n <= 62
    bits = []
    for j in range(n):
        for i in range(j):
            bits.append((adj[i] >> j) & 1)
    while len(bits) % 6 != 0:
        bits.append(0)
    chars = [chr(n + 63)]
    for pos in range(0, len(bits), 6):
        v = 0
        for b in bits[pos:pos + 6]:
            v = (v << 1) | b
        chars.append(chr(v + 63))
    return "".join(chars)


def enum_indep(adj: list[int], k: int, limit: int | None = None) -> list[int]:
    """Enumerate independent k-sets in a bitmask graph."""
    n = len(adj)
    res: list[int] = []

    def dfs(cand: int, rem: int, cur: int) -> None:
        if limit is not None and len(res) >= limit:
            return
        if rem == 0:
            res.append(cur)
            return
        while cand.bit_count() >= rem:
            if limit is not None and len(res) >= limit:
                return
            b = cand & -cand
            v = b.bit_length() - 1
            cand ^= b
            dfs(cand & ~adj[v], rem - 1, cur | b)

    dfs((1 << n) - 1, k, 0)
    return res


def verify_r38_26(adj: list[int], expected_edges: int | None = None, check_alpha: bool = True) -> dict:
    """Strictly verify a 26-vertex (3, 8; 26) triangle-free core graph."""
    assert len(adj) == N_T, f"Expected {N_T} vertices, got {len(adj)}"
    edges = sum(x.bit_count() for x in adj) // 2
    if expected_edges is not None:
        assert edges == expected_edges, f"Expected {expected_edges} edges, got {edges}"
    else:
        assert 73 <= edges <= 81, f"Edge count {edges} outside valid D9-C6 range [73, 81]"

    degs = [x.bit_count() for x in adj]
    assert min(degs) >= 3 and max(degs) <= 7, f"Degree bounds violated: min={min(degs)}, max={max(degs)}"
    for i in range(N_T):
        assert not ((adj[i] >> i) & 1), f"Self-loop on vertex {i}"
        for j in range(i + 1, N_T):
            assert ((adj[i] >> j) & 1) == ((adj[j] >> i) & 1), f"Asymmetric edge ({i},{j})"
            if (adj[i] >> j) & 1:
                assert (adj[i] & adj[j]) == 0, f"Triangle on edge ({i},{j})"
    if check_alpha:
        assert len(enum_indep(adj, 8, limit=1)) == 0, "Core graph has an independent 8-set (alpha >= 8)"
    return {"edges": edges, "min_deg": min(degs), "max_deg": max(degs)}


def load_and_filter_cores(
    g6_path: Path,
    allowed_edges: set[int] | None = None,
    verify_alpha: bool = True,
) -> tuple[dict[int, list[str]], dict]:
    """Stream a .g6 or .g6.gz file of 26-vertex cores and filter by exact D9-C6 edge/degree bounds."""
    if allowed_edges is None:
        allowed_edges = set(range(73, 82))
    by_edges: dict[int, list[str]] = {e: [] for e in sorted(allowed_edges)}
    seen: set[str] = set()
    total_scanned = 0
    edge_matched = 0
    degree_rejected = 0

    opener = gzip.open if str(g6_path).endswith(".gz") else open
    with opener(g6_path, "rt", encoding="ascii") as fp:
        for line in fp:
            s = line.strip().removeprefix(">>graph6<<")
            if not s:
                continue
            assert len(s) == G6_LEN_26 and ord(s[0]) - 63 == N_T, (
                f"Invalid 26-vertex graph6 line (len={len(s)}, n={ord(s[0]) - 63}): {s[:20]}"
            )
            total_scanned += 1
            e = sum((ord(ch) - 63).bit_count() for ch in s[1:])
            if e not in allowed_edges:
                continue
            edge_matched += 1
            if s in seen:
                continue
            adj = decode_g6(s)
            degs = [x.bit_count() for x in adj]
            if min(degs) < 3 or max(degs) > 7:
                degree_rejected += 1
                continue
            verify_r38_26(adj, expected_edges=e, check_alpha=verify_alpha)
            seen.add(s)
            by_edges[e].append(s)

    stats = {
        "total_scanned": total_scanned,
        "edge_matched": edge_matched,
        "degree_rejected": degree_rejected,
        "unique_valid_cores": len(seen),
        "counts_by_edges": {str(e): len(gs) for e, gs in by_edges.items()},
    }
    return by_edges, stats


class CompactCNF:
    """Minimal zero-dependency DIMACS CNF builder with Sinz sequential counters & lex constraints."""

    def __init__(self, start_var: int = 1):
        self.nv = start_var - 1
        self.clauses: list[list[int]] = []

    def var(self) -> int:
        self.nv += 1
        return self.nv

    def add(self, cl: list[int]) -> None:
        self.clauses.append(list(cl))

    def atmost_seq(self, xs: list[int], k: int) -> None:
        m = len(xs)
        if k < 0:
            self.add([])
            return
        if k >= m:
            return
        if k == 0:
            for x in xs:
                self.add([-x])
            return
        # Sinz sequential counter (exact upper bound <= k)
        s = [[self.var() for _ in range(k)] for _ in range(m - 1)]
        self.add([-xs[0], s[0][0]])
        for j in range(1, k):
            self.add([-s[0][j]])
        for i in range(1, m - 1):
            self.add([-xs[i], s[i][0]])
            self.add([-s[i - 1][0], s[i][0]])
            for j in range(1, k):
                self.add([-xs[i], -s[i - 1][j - 1], s[i][j]])
                self.add([-s[i - 1][j], s[i][j]])
            self.add([-xs[i], -s[i - 1][k - 1]])
        self.add([-xs[m - 1], -s[m - 2][k - 1]])

    def atleast_seq(self, xs: list[int], k: int) -> None:
        if k <= 0:
            return
        if k == 1:
            self.add(list(xs))
            return
        self.atmost_seq([-x for x in xs], len(xs) - k)

    def exact_seq(self, xs: list[int], k: int) -> None:
        self.atmost_seq(xs, k)
        self.atleast_seq(xs, k)

    def lex_lt(self, a: list[int], b: list[int]) -> None:
        """Enforce bitvector a < b strictly (MSB at index 0)."""
        assert len(a) == len(b)
        p = None
        for x, y in zip(a, b):
            pre = [] if p is None else [-p]
            self.add(pre + [-x, y])
            z = self.var()
            if p is not None:
                self.add([-z, p])
            self.add([-z, -x, y])
            self.add([-z, x, -y])
            self.add(pre + [-x, -y, z])
            self.add(pre + [x, y, z])
            p = z
        assert p is not None
        self.add([-p])

    def lex_le(self, a: list[int], b: list[int]) -> None:
        """Enforce bitvector a <= b non-strictly (MSB at index 0)."""
        assert len(a) == len(b)
        p = None
        for idx, (x, y) in enumerate(zip(a, b)):
            pre = [] if p is None else [-p]
            self.add(pre + [-x, y])
            if idx + 1 < len(a):
                z = self.var()
                if p is not None:
                    self.add([-z, p])
                self.add([-z, -x, y])
                self.add([-z, x, -y])
                self.add(pre + [-x, -y, z])
                self.add(pre + [x, y, z])
                p = z

    def write_dimacs(self, path: Path, extra_clauses: list[list[int]] = ()) -> None:
        total = len(self.clauses) + len(extra_clauses)
        with open(path, "w", encoding="ascii") as f:
            f.write(f"p cnf {self.nv} {total}\n")
            for cl in self.clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")
            for cl in extra_clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")


def build_d9c6_cnf(
    adj: list[int],
    orbit: dict,
    include_b2: bool = True,
    include_i7: bool = True,
    include_lex: bool = True,
    max_i7: int | None = None,
    verify_core: bool = True,
) -> tuple[CompactCNF, list[list[int]], dict]:
    """Build the compact 312-variable DIMACS CNF for one (core T, canonical orbit H) pair."""
    if verify_core:
        verify_r38_26(adj, expected_edges=orbit["e_T"], check_alpha=True)
    else:
        assert sum(x.bit_count() for x in adj) // 2 == orbit["e_T"]

    edges_T = [(i, j) for i in range(N_T) for j in range(i + 1, N_T) if (adj[i] >> j) & 1]
    deg = [x.bit_count() for x in adj]
    rem = [9 - d for d in deg]
    assert min(deg) >= orbit["min_deg_T"], (
        f"Core min_deg={min(deg)} < orbit {orbit['id']} min_deg_T={orbit['min_deg_T']}"
    )

    adj_x: list[int] = orbit["adj_x"]
    adj_y: list[int] = orbit["adj_y"]
    deg_T_X: list[int] = orbit["deg_T_X"]
    deg_T_Y: list[int] = orbit["deg_T_Y"]
    alpha_h: int = orbit["alpha_H"]
    alpha_both_h: int = orbit["alpha_both_H"]

    cnf = CompactCNF(1)
    # Primary variables 1..312: M[r][t] = r * 26 + t + 1
    # Rows 0..5 = S, 6..8 = X, 9..11 = Y
    M = [[cnf.var() for _ in range(N_T)] for _ in range(NUM_ROWS)]
    assert cnf.nv == NUM_PRIMARY_VARS

    A_rows = list(range(9))  # S (0..5) + X (6..8)
    B_rows = list(range(6)) + [9, 10, 11]  # S (0..5) + Y (9..11)

    # 1. Triangle-free with T
    for r in range(NUM_ROWS):
        for u, v in edges_T:
            cnf.add([-M[r][u], -M[r][v]])

    # 2. Triangle-free with H = G[X, Y]
    for i in range(3):
        for j in range(3):
            if (adj_x[i] >> j) & 1:
                for t in range(N_T):
                    cnf.add([-M[6 + i][t], -M[9 + j][t]])

    # 3. Exact row degrees
    for s in range(NUM_S):
        cnf.exact_seq(M[s], 7)
    for i in range(NUM_X):
        cnf.exact_seq(M[6 + i], deg_T_X[i])
    for j in range(NUM_Y):
        cnf.exact_seq(M[9 + j], deg_T_Y[j])

    # 4. Exact column degrees + A/B bounds (1 <= d_A, d_B <= 6) + generalized S-domination
    s_dom_enforced = 0
    for t in range(N_T):
        cnf.exact_seq([M[r][t] for r in range(NUM_ROWS)], rem[t])
        # d_A(t) in [1, 6] and d_B(t) in [1, 6]
        col_A = [M[r][t] for r in A_rows]
        col_B = [M[r][t] for r in B_rows]
        cnf.atleast_seq(col_A, 1)
        cnf.atmost_seq(col_A, 6)
        cnf.atleast_seq(col_B, 1)
        cnf.atmost_seq(col_B, 6)
        # Exact generalized S-domination
        min_ds = max(1 if rem[t] > alpha_both_h else 0, rem[t] - alpha_h)
        if min_ds > 0:
            s_dom_enforced += 1
            cnf.atleast_seq([M[s][t] for s in range(NUM_S)], min_ds)

    # 5. Exact saturation (non-edge codegree >= 1)
    for t in range(N_T):
        nbrs_t = [u for u in range(N_T) if (adj[t] >> u) & 1]
        # S -> T: N(s) & N(t) = N_T(s) & N_T(t)
        for s in range(NUM_S):
            cnf.add([M[s][t]] + [M[s][u] for u in nbrs_t])
        # X -> T: N(x_i) & N(t) = (N_Y(x_i) & N_Y(t)) U (N_T(x_i) & N_T(t))
        for i in range(NUM_X):
            ynbrs = [9 + j for j in range(3) if (adj_x[i] >> j) & 1]
            cnf.add([M[6 + i][t]] + [M[yr][t] for yr in ynbrs] + [M[6 + i][u] for u in nbrs_t])
        # Y -> T: symmetric
        for j in range(NUM_Y):
            xnbrs = [6 + i for i in range(3) if (adj_y[j] >> i) & 1]
            cnf.add([M[9 + j][t]] + [M[xr][t] for xr in xnbrs] + [M[9 + j][u] for u in nbrs_t])

    # 6. Pairwise non-edge codegree caps (<= 6) + nonadjacent (X, Y) saturation (>= 1)
    def add_pair_cap(r1: int, r2: int, cap: int, require_ge1: bool = False) -> None:
        bs = []
        for t in range(N_T):
            b = cnf.var()
            cnf.add([-M[r1][t], -M[r2][t], b])
            if require_ge1:
                cnf.add([-b, M[r1][t]])
                cnf.add([-b, M[r2][t]])
            bs.append(b)
        if cap < N_T:
            cnf.atmost_seq(bs, cap)
        if require_ge1:
            cnf.atleast_seq(bs, 1)

    # (S, S): cap 4
    for i in range(NUM_S):
        for j in range(i + 1, NUM_S):
            add_pair_cap(i, j, 4)

    # (S, X) and (S, Y): cap 5 (only when deg_T(x/y) >= 6)
    for s in range(NUM_S):
        for i in range(NUM_X):
            if deg_T_X[i] > 5:
                add_pair_cap(s, 6 + i, 5)
        for j in range(NUM_Y):
            if deg_T_Y[j] > 5:
                add_pair_cap(s, 9 + j, 5)

    # (X, X): cap 5 - |N_Y(x_i) & N_Y(x_j)|
    for i in range(NUM_X):
        for j in range(i + 1, NUM_X):
            cap = 5 - (adj_x[i] & adj_x[j]).bit_count()
            if min(deg_T_X[i], deg_T_X[j]) > cap:
                add_pair_cap(6 + i, 6 + j, cap)

    # (Y, Y): cap 5 - |N_X(y_i) & N_X(y_j)|
    for i in range(NUM_Y):
        for j in range(i + 1, NUM_Y):
            cap = 5 - (adj_y[i] & adj_y[j]).bit_count()
            if min(deg_T_Y[i], deg_T_Y[j]) > cap:
                add_pair_cap(9 + i, 9 + j, cap)

    # Nonadjacent (X, Y) pairs: |N_T(x_i) & N_T(y_j)| in [1, 6]
    nonadj_xy_pairs = 0
    for i in range(NUM_X):
        for j in range(NUM_Y):
            if not ((adj_x[i] >> j) & 1):
                nonadj_xy_pairs += 1
                need_cap = min(deg_T_X[i], deg_T_Y[j]) > 6
                add_pair_cap(6 + i, 9 + j, 6 if need_cap else N_T, require_ge1=True)

    # Zero-redundant nonadjacent T-pair codegree caps & zero-codeg T-pair saturation
    nontrivial_t_pairs = 0
    zero_codeg_t_pairs = 0
    for u in range(N_T):
        for v in range(u + 1, N_T):
            if (adj[u] >> v) & 1:
                continue
            ct = (adj[u] & adj[v]).bit_count()
            cap = 6 - ct
            need_cap = min(rem[u], rem[v]) > cap
            need_sat = (ct == 0)
            if need_cap or need_sat:
                if need_cap:
                    nontrivial_t_pairs += 1
                if need_sat:
                    zero_codeg_t_pairs += 1
                bs = []
                for r in range(NUM_ROWS):
                    b = cnf.var()
                    cnf.add([-M[r][u], -M[r][v], b])
                    if need_sat:
                        cnf.add([-b, M[r][u]])
                        cnf.add([-b, M[r][v]])
                    bs.append(b)
                if need_cap:
                    cnf.atmost_seq(bs, cap)
                if need_sat:
                    cnf.atleast_seq(bs, 1)

    # 7. Exact Hall b=1 private-neighbor bounds (for ALL rows in A and ALL rows in B)
    for grp in (A_rows, B_rows):
        for r in grp:
            other = [q for q in grp if q != r]
            priv = []
            for t in range(N_T):
                p = cnf.var()
                cnf.add([-M[r][t], p] + [M[q][t] for q in other])
                priv.append(p)
            cnf.atmost_seq(priv, 1)

    # 8. Optional Hall b=2 bounds (<= 3 vertices in T with N_A(t) subset {r1, r2})
    if include_b2:
        for grp in (A_rows, B_rows):
            for idx1 in range(len(grp)):
                for idx2 in range(idx1 + 1, len(grp)):
                    r1, r2 = grp[idx1], grp[idx2]
                    omit = [q for q in grp if q != r1 and q != r2]
                    hs = []
                    for t in range(N_T):
                        h = cnf.var()
                        cnf.add([h] + [M[q][t] for q in omit])
                        hs.append(h)
                    cnf.atmost_seq(hs, 3)

    # 9. Optional static I_7(T) hitting-set constraints
    i7_total = 0
    i7_encoded = 0
    if include_i7:
        I7 = enum_indep(adj, 7)
        i7_total = len(I7)
        use_i7 = I7 if max_i7 is None else I7[:max_i7]
        i7_encoded = len(use_i7)
        for w in use_i7:
            vs = [t for t in range(N_T) if (w >> t) & 1]
            ms = []
            for r in range(NUM_ROWS):
                z = cnf.var()
                cnf.add([z] + [M[r][t] for t in vs])
                ms.append(z)
            cnf.atmost_seq([ms[r] for r in A_rows], 2)
            cnf.atmost_seq([ms[r] for r in B_rows], 2)

    # 10. Sound automorphism-respecting symmetry breaking
    sym_constraints = []
    if include_lex:
        # Strict lex on S (6 rows)
        for i in range(NUM_S - 1):
            cnf.lex_lt(M[i], M[i + 1])
            sym_constraints.append(f"S[{i}]<S[{i+1}]")
        # Strict lex within twin classes of X
        for cls in orbit["twin_classes_X"]:
            for a_i, b_i in zip(cls, cls[1:]):
                cnf.lex_lt(M[6 + a_i], M[6 + b_i])
                sym_constraints.append(f"X[{a_i}]<X[{b_i}]")
        # Strict lex within twin classes of Y
        for cls in orbit["twin_classes_Y"]:
            for a_j, b_j in zip(cls, cls[1:]):
                cnf.lex_lt(M[9 + a_j], M[9 + b_j])
                sym_constraints.append(f"Y[{a_j}]<Y[{b_j}]")
        # Non-strict X[0] <= Y[0] when canonical H is transpose-symmetric
        if orbit["transpose_symmetric"]:
            cnf.lex_le(M[6], M[9])
            sym_constraints.append("X[0]<=Y[0]")

    meta = {
        "orbit_id": orbit["id"],
        "e_xy": orbit["e_xy"],
        "e_T": orbit["e_T"],
        "primary_vars": NUM_PRIMARY_VARS,
        "vars": cnf.nv,
        "clauses": len(cnf.clauses),
        "s_dom_enforced": s_dom_enforced,
        "nonadj_xy_pairs": nonadj_xy_pairs,
        "nontrivial_t_pairs": nontrivial_t_pairs,
        "zero_codeg_t_pairs": zero_codeg_t_pairs,
        "i7_total": i7_total,
        "i7_encoded": i7_encoded,
        "include_b2": include_b2,
        "include_i7": include_i7,
        "include_lex": include_lex,
        "sym_constraints": sym_constraints,
    }
    return cnf, M, meta


def build_40_graph(adj_T: list[int], orbit: dict, rows: list[int]) -> list[int]:
    """Reconstruct the full 40-vertex graph from T (26 verts), orbit H, and 12 row bitmasks."""
    assert len(adj_T) == N_T and len(rows) == NUM_ROWS
    g = [0] * N_G

    def add_e(u: int, v: int) -> None:
        g[u] |= 1 << v
        g[v] |= 1 << u

    # S = 2..7, X = 8..10, Y = 11..13, T = 14..39
    for s in range(2, 8):
        add_e(0, s)
        add_e(1, s)
    for i in range(3):
        add_e(0, 8 + i)
    for j in range(3):
        add_e(1, 11 + j)
    for i in range(3):
        for j in range(3):
            if (orbit["adj_x"][i] >> j) & 1:
                add_e(8 + i, 11 + j)
    for i in range(N_T):
        for j in range(i + 1, N_T):
            if (adj_T[i] >> j) & 1:
                add_e(14 + i, 14 + j)
    for r in range(NUM_ROWS):
        u = 2 + r
        m = rows[r]
        for t in range(N_T):
            if (m >> t) & 1:
                add_e(u, 14 + t)
    return g


def verify_40_witness(g40: list[int], orbit: dict | None = None, check_max_codeg: bool = True) -> dict:
    """Independent strict verifier for a candidate 40-vertex (3, 10; 40) D9-C6 witness."""
    if len(g40) != N_G:
        return {"ok": False, "reason": f"vertex_count={len(g40)}"}
    for i in range(N_G):
        if (g40[i] >> i) & 1:
            return {"ok": False, "reason": f"self_loop:{i}"}
        if g40[i].bit_count() != 9:
            return {"ok": False, "reason": f"degree:{i}:{g40[i].bit_count()}"}
        for j in range(i + 1, N_G):
            eij = (g40[i] >> j) & 1
            eji = (g40[j] >> i) & 1
            if eij != eji:
                return {"ok": False, "reason": f"asymmetric:{i},{j}"}
            if eij and (g40[i] & g40[j]):
                return {"ok": False, "reason": f"triangle:{i},{j}"}

    if check_max_codeg:
        if (g40[0] >> 1) & 1:
            return {"ok": False, "reason": "roots_adjacent"}
        root_codeg = (g40[0] & g40[1]).bit_count()
        if root_codeg != 6:
            return {"ok": False, "reason": f"root_codeg:{root_codeg}"}
        max_c = 0
        for i in range(N_G):
            for j in range(i + 1, N_G):
                if not ((g40[i] >> j) & 1):
                    c = (g40[i] & g40[j]).bit_count()
                    if c > max_c:
                        max_c = c
        if max_c > 6:
            return {"ok": False, "reason": f"max_nonedge_codeg:{max_c}"}

    if orbit is not None:
        for i in range(3):
            for j in range(3):
                got = (g40[8 + i] >> (11 + j)) & 1
                exp = (orbit["adj_x"][i] >> j) & 1
                if got != exp:
                    return {"ok": False, "reason": f"skeleton_mismatch:{i},{j}"}

    i10 = enum_indep(g40, 10, limit=1)
    if i10:
        return {"ok": False, "reason": "has_I10", "sample_i10": i10[0]}

    return {"ok": True, "vertices": N_G, "edges": sum(x.bit_count() for x in g40) // 2}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def write_atomic_json(path: Path, obj: dict) -> None:
    tmp = path.with_suffix(".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(json.dumps(obj, indent=2) + "\n")
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)


def proof_first_solve_instance(
    g6: str,
    orbit: dict,
    out_dir: Path,
    seconds: int = 1800,
    include_b2: bool = True,
    include_i7: bool = True,
    include_lex: bool = True,
    max_i7: int | None = None,
    compress_cnf: bool = True,
    try_lrat: bool = True,
    instance_id: str | None = None,
) -> dict:
    """Single-pass proof-first Kissat + drat-trim (+ optional lrat-check) solver for one (core, orbit)."""
    out_dir.mkdir(parents=True, exist_ok=True)
    adj = decode_g6(g6)
    cnf, M, meta = build_d9c6_cnf(
        adj,
        orbit,
        include_b2=include_b2,
        include_i7=include_i7,
        include_lex=include_lex,
        max_i7=max_i7,
        verify_core=True,
    )
    extra_cuts: list[list[int]] = []
    seen_cuts: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    t0 = time.monotonic()
    iters = 0
    report: dict = {
        "instance_id": instance_id or f"{orbit['id']}_e{orbit['e_T']}",
        "orbit_id": orbit["id"],
        "e_xy": orbit["e_xy"],
        "e_T": orbit["e_T"],
        "g6": g6,
        "meta": meta,
        "status": "OPEN",
        "iters": 0,
        "cuts": 0,
    }

    while time.monotonic() - t0 < seconds:
        iters += 1
        rem_sec = max(5, int(seconds - (time.monotonic() - t0)))
        cnf_path = out_dir / "leaf.cnf"
        drat_path = out_dir / "leaf.drat"
        lrat_path = out_dir / "leaf.lrat"
        cnf.write_dimacs(cnf_path, extra_cuts)

        def cap_fsize() -> None:
            resource.setrlimit(resource.RLIMIT_FSIZE, (1024 * 1024 ** 2, 1024 * 1024 ** 2))

        t_solve0 = time.monotonic()
        try:
            with open(out_dir / "kissat.log", "w", encoding="utf-8") as log:
                r = subprocess.run(
                    ["kissat", f"--time={rem_sec}", str(cnf_path), str(drat_path)],
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    timeout=rem_sec + 30,
                    preexec_fn=cap_fsize,
                )
        except subprocess.TimeoutExpired:
            drat_path.unlink(missing_ok=True)
            cnf_path.unlink(missing_ok=True)
            report.update(status="OPEN_TIMEOUT", iters=iters, cuts=len(extra_cuts))
            break

        solve_sec = time.monotonic() - t_solve0
        if r.returncode == 20:
            cnf_sha = sha256_file(cnf_path)
            drat_sha = sha256_file(drat_path)
            drat_bytes = drat_path.stat().st_size
            t_ver0 = time.monotonic()

            drat_cmd = ["drat-trim", str(cnf_path), str(drat_path)]
            if try_lrat:
                drat_cmd += ["-L", str(lrat_path)]

            ok_drat = False
            ok_lrat = False
            lrat_sha = None
            lrat_bytes = None
            try:
                with open(out_dir / "drat-trim.log", "w", encoding="utf-8") as log:
                    v = subprocess.run(
                        drat_cmd,
                        stdout=log,
                        stderr=subprocess.STDOUT,
                        timeout=max(120, rem_sec),
                    )
                ok_drat = (
                    v.returncode == 0
                    and "s VERIFIED" in (out_dir / "drat-trim.log").read_text(errors="replace")
                )
                if ok_drat and try_lrat and lrat_path.is_file() and shutil.which("lrat-check"):
                    with open(out_dir / "lrat-check.log", "w", encoding="utf-8") as log:
                        lv = subprocess.run(
                            ["lrat-check", str(cnf_path), str(lrat_path)],
                            stdout=log,
                            stderr=subprocess.STDOUT,
                            timeout=max(120, rem_sec),
                        )
                    ok_lrat = (
                        lv.returncode == 0
                        and "s VERIFIED" in (out_dir / "lrat-check.log").read_text(errors="replace")
                    )
                    if ok_lrat:
                        lrat_sha = sha256_file(lrat_path)
                        lrat_bytes = lrat_path.stat().st_size
                        with open(lrat_path, "rb") as fi, gzip.open(
                            out_dir / "leaf.lrat.gz", "wb", compresslevel=1
                        ) as fo:
                            shutil.copyfileobj(fi, fo)
            except subprocess.TimeoutExpired:
                ok_drat = False

            ver_sec = time.monotonic() - t_ver0
            if ok_drat:
                with open(drat_path, "rb") as fi, gzip.open(
                    out_dir / "leaf.drat.gz", "wb", compresslevel=1
                ) as fo:
                    shutil.copyfileobj(fi, fo)
                cnf_gz_sha = None
                if compress_cnf:
                    with open(cnf_path, "rb") as fi, gzip.open(
                        out_dir / "leaf.cnf.gz", "wb", compresslevel=1
                    ) as fo:
                        shutil.copyfileobj(fi, fo)
                    cnf_gz_sha = sha256_file(out_dir / "leaf.cnf.gz")
                report.update(
                    status="CERTIFIED_UNSAT",
                    iters=iters,
                    cuts=len(extra_cuts),
                    cnf_sha256=cnf_sha,
                    cnf_gz_sha256=cnf_gz_sha,
                    drat_sha256=drat_sha,
                    drat_bytes=drat_bytes,
                    lrat_verified=ok_lrat,
                    lrat_sha256=lrat_sha,
                    lrat_bytes=lrat_bytes,
                    solve_seconds=round(solve_sec, 3),
                    verify_seconds=round(ver_sec, 3),
                )
            else:
                report.update(
                    status="UNSAT_VERIFICATION_FAILED",
                    iters=iters,
                    cuts=len(extra_cuts),
                    solve_seconds=round(solve_sec, 3),
                    verify_seconds=round(ver_sec, 3),
                )
            drat_path.unlink(missing_ok=True)
            lrat_path.unlink(missing_ok=True)
            cnf_path.unlink(missing_ok=True)
            break

        elif r.returncode == 10:
            drat_path.unlink(missing_ok=True)
            vals: set[int] = set()
            for line in (out_dir / "kissat.log").read_text(errors="replace").splitlines():
                if line.startswith("v "):
                    for tok in line.split()[1:]:
                        lit = int(tok)
                        if 1 <= lit <= NUM_PRIMARY_VARS:
                            vals.add(lit)
            rows = [
                sum((1 << t) for t in range(N_T) if M[r_idx][t] in vals)
                for r_idx in range(NUM_ROWS)
            ]
            g40 = build_40_graph(adj, orbit, rows)
            i10s = enum_indep(g40, 10, limit=128)
            if not i10s:
                vcheck = verify_40_witness(g40, orbit=orbit, check_max_codeg=True)
                assert vcheck["ok"], f"Internal witness verification failed: {vcheck}"
                (out_dir / "witness.txt").write_text(
                    "".join(
                        "".join(str((g40[i] >> j) & 1) for j in range(N_G)) + "\n"
                        for i in range(N_G)
                    ),
                    encoding="ascii",
                )
                write_atomic_json(out_dir / "witness-check.json", vcheck)
                report.update(
                    status="VERIFIED_WITNESS",
                    iters=iters,
                    cuts=len(extra_cuts),
                    witness_check=vcheck,
                )
                cnf_path.unlink(missing_ok=True)
                break

            added = 0
            for mask in i10s:
                rs = tuple(v - 2 for v in range(2, 14) if (mask >> v) & 1)
                ts = tuple(v - 14 for v in range(14, 40) if (mask >> v) & 1)
                key = (rs, ts)
                if key not in seen_cuts:
                    seen_cuts.add(key)
                    cl = [M[r_idx][t_idx] for r_idx in rs for t_idx in ts]
                    assert cl, "Empty I10 cut!"
                    extra_cuts.append(cl)
                    added += 1
            assert added > 0, "SAT model had I10s but no new cuts were generated"
            report.update(iters=iters, cuts=len(extra_cuts))
        else:
            drat_path.unlink(missing_ok=True)
            cnf_path.unlink(missing_ok=True)
            report.update(
                status="OPEN_TIMEOUT",
                kissat_exit=r.returncode,
                iters=iters,
                cuts=len(extra_cuts),
            )
            break

    report["total_seconds"] = round(time.monotonic() - t0, 3)
    write_atomic_json(out_dir / "result.json", report)
    print(json.dumps(report), flush=True)
    return report


def main() -> None:
    p = argparse.ArgumentParser(description="D9-C6 Compact 312-var Proof-First CNF Solver")
    p.add_argument("--list-orbits", action="store_true", help="Print all 25 canonical D9-C6 orbits as JSON")
    p.add_argument("--g6", help="Single 26-vertex (3,8;26) graph6 string")
    p.add_argument("--orbit", help="Canonical orbit ID (e.g. D9-C6-S00)")
    p.add_argument("--out", default="out_d9c6", help="Output directory")
    p.add_argument("--seconds", type=int, default=1800, help="Solve budget in seconds")
    p.add_argument("--no-b2", action="store_true", help="Disable Hall b=2 constraints")
    p.add_argument("--no-i7", action="store_true", help="Disable static I7 hitting-set constraints")
    p.add_argument("--no-lex", action="store_true", help="Disable symmetry-breaking constraints")
    p.add_argument("--no-lrat", action="store_true", help="Skip LRAT extraction / lrat-check")
    p.add_argument("--max-i7", type=int, default=None, help="Optional cap on encoded I7 sets")
    a = p.parse_args()

    orbits = enumerate_d9c6_skeletons()
    if a.list_orbits:
        print(json.dumps(orbits, indent=2))
        return
    if a.g6 and a.orbit:
        by_id = {o["id"]: o for o in orbits}
        assert a.orbit in by_id, f"Unknown orbit ID: {a.orbit}"
        proof_first_solve_instance(
            a.g6,
            by_id[a.orbit],
            Path(a.out),
            seconds=a.seconds,
            include_b2=not a.no_b2,
            include_i7=not a.no_i7,
            include_lex=not a.no_lex,
            max_i7=a.max_i7,
            try_lrat=not a.no_lrat,
        )
    else:
        p.print_help()


if __name__ == "__main__":
    main()
