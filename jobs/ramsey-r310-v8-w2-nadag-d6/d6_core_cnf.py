#!/usr/bin/env python3
r"""Compact Fixed-Core DIMACS CNF Encoder, Proof-First Kissat/DRAT/LRAT Worker,
and Independent SAT Witness Verifier for Unified NA-DAG Tier-1 D6 (delta(G) = 6).

Mirrors d9c7_compact_cnf.py's winning 1-pass fixed-core structure for all 9 Tier-1 D6
non-adjacent-root branches:
  - r = 5 (n_T = 27, e(T) in [85, 92]): D6-R5-Q6 (c=1), Q7 (c=2), Q8 (c=3), Q9 (c=4)
  - r = 6 (n_T = 26, e(T) in [73, 84]): D6-R6-Q7 (c=1), Q8 (c=2), Q9 (c=3)
  - r = 7 (n_T = 25, e(T) in [65, 76]): D6-R7-Q8 (c=1), Q9 (c=2)

For a fixed (3, 8; n_T) core T (triangle-free, alpha(T) <= 7), the 40-vertex graph W is
completely determined by:
  - M[i][t] for i in S U X U Y (R = 6 + r rows, 11..13) and t in T (n_T = 25..27)
  - E_XY[ix][iy] for ix in X (n_X = 6 - c), iy in Y (n_Y = r)
yielding only 307..360 primary Boolean edge variables.

All encoded constraints are proved necessary conditions (100% sound, zero heuristic pruning):
  1. Triangle-freeness with T and across X-Y-T.
  2. Mandatory X-Y saturation (deg_Y(x) >= 1, deg_X(y) >= 1) and exact pruner t-range.
  3. Exact vertex degree bounds deg_W(w) in [6, 9], plus deg_T(x) <= 7, deg_T(y) <= 7.
  4. Exact A-domination and B-domination on T (plus S-domination when X-Y is complete).
  5. Exact non-edge saturation S -> T, X -> T, Y -> T.
  6. Exact pairwise codegree caps on S (<= 5 in T) and nontrivial non-adjacent T-pairs.
  7. Exact Hall b=1 private-neighbor caps on A (<= 4) and B (<= 10 - q).
  8. Exact static I_7(T) hitting-set constraints:
       - at most 2 of A = S U X miss W_7
       - at most 2 of B = S U Y miss W_7
       - at most 1 of X misses W_7 (since W_7 U R_X U {v} is independent!)
       - at most 1 of Y misses W_7 (since W_7 U R_Y U {u} is independent!)
  9. Exact e(H_u) in [118, 127] and e(H_v) in [E9[q], eH_hi(q)] edge-sum bounds.
 10. Sound strict lex_lt symmetry breaking within S, within X, and within Y.
"""
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

N_G = 40
E9 = {6: 118, 7: 104, 8: 95, 9: 86}
E8 = {21: 35, 22: 42, 23: 49, 24: 56, 25: 65, 26: 73, 27: 85}
E8MAX = {23: 80, 24: 84, 25: 87, 26: 91, 27: 94}


def decode_g6(raw: str, expected_n=None):
    s = raw.strip().removeprefix(">>graph6<<")
    n = ord(s[0]) - 63
    if expected_n is not None:
        assert n == expected_n, f"Expected n={expected_n}, got {n}"
    assert len(s) == 1 + (n * (n - 1) // 2 + 5) // 6, f"Bad graph6 length: {s[:20]}"
    adj = [0] * n
    k = 0
    for j in range(n):
        for i in range(j):
            if ((ord(s[1 + k // 6]) - 63) >> (5 - k % 6)) & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return adj


def encode_g6(adj):
    n = len(adj)
    assert 1 <= n <= 62
    bits = []
    for j in range(n):
        for i in range(j):
            bits.append((adj[i] >> j) & 1)
    while len(bits) % 6 != 0:
        bits.append(0)
    chars = [chr(n + 63)]
    for k in range(0, len(bits), 6):
        val = 0
        for b in bits[k : k + 6]:
            val = (val << 1) | b
        chars.append(chr(val + 63))
    return "".join(chars)


def enum_indep(adj, k, limit=None):
    n = len(adj)
    res = []

    def dfs(cand, rem, cur):
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


def verify_r38_core(adj, expected_n=None):
    n = len(adj)
    if expected_n is not None:
        assert n == expected_n, f"Expected n_T={expected_n}, got {n}"
    edges = sum(x.bit_count() for x in adj) // 2
    for i in range(n):
        assert not ((adj[i] >> i) & 1), f"Self-loop at {i}"
        for j in range(i + 1, n):
            assert ((adj[i] >> j) & 1) == ((adj[j] >> i) & 1), f"Asymmetric ({i},{j})"
            if (adj[i] >> j) & 1:
                assert (adj[i] & adj[j]) == 0, f"Triangle on ({i},{j})"
    assert len(enum_indep(adj, 8, limit=1)) == 0, "Core has an independent 8-set (alpha > 7)"
    return edges


class CompactCNF:
    def __init__(self, start_var=1):
        self.nv = start_var - 1
        self.clauses = []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        self.clauses.append(list(cl))

    def atmost_seq(self, xs, k):
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

    def atleast_seq(self, xs, k):
        if k <= 0:
            return
        if k > len(xs):
            self.add([])
            return
        if k == 1:
            self.add(list(xs))
            return
        self.atmost_seq([-x for x in xs], len(xs) - k)

    def exact_seq(self, xs, k):
        self.atmost_seq(xs, k)
        self.atleast_seq(xs, k)

    def range_seq(self, xs, lo, hi):
        if lo > hi:
            self.add([])
            return
        if lo > 0:
            self.atleast_seq(xs, lo)
        if hi < len(xs):
            self.atmost_seq(xs, hi)

    def lex_lt(self, a, b):
        """Enforce bitvector a < b strictly (MSB at index 0)."""
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
        self.add([-p])

    def write_dimacs(self, path: Path, extra_clauses=()):
        total = len(self.clauses) + len(extra_clauses)
        with open(path, "w") as f:
            f.write(f"p cnf {self.nv} {total}\n")
            for cl in self.clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")
            for cl in extra_clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")


def build_d6_core_cnf(
    adj_T,
    r: int,
    q: int,
    t_bounds=None,
    include_i7: bool = True,
    max_i7: int = 2000,
    include_lex: bool = True,
    verify_core: bool = True,
):
    """Build compact fixed-core CNF for Tier-1 D6 branch (r, q) on fixed core T.

    Parameters:
      adj_T: list of int adjacency bitmasks of length n_T = 32 - r
      r: internal degree deg_{H_u}(v) in {5, 6, 7}
      q: W-degree deg_W(v) in {r+1, ..., 9}
      t_bounds: optional (t_lo, t_hi) from d6_nadag_pruner for this (r, q, e(T))
      include_i7: include static I_7(T) hitting-set constraints
      max_i7: cap on I_7(T) sets encoded statically (0 = unlimited; default 2000)
      include_lex: include sound strict lex symmetry breaking on S, X, Y
      verify_core: verify adj_T is triangle-free with alpha(T) <= 7
    """
    assert r in (5, 6, 7) and r + 1 <= q <= 9
    c = q - r
    nx = 6 - c
    ny = r
    nt = 32 - r
    R = 6 + r  # |S| + |X| + |Y| = c + (6 - c) + r = 6 + r
    assert len(adj_T) == nt

    eT = verify_r38_core(adj_T, nt) if verify_core else (sum(x.bit_count() for x in adj_T) // 2)
    eT_lo = E8[nt]
    eT_hi = min(E8MAX[nt], 132 - 8 * r)
    if not (eT_lo <= eT <= eT_hi):
        return None, None, None, dict(unsat_by_pruner=True, reason=f"eT={eT} outside [{eT_lo},{eT_hi}]")

    t_lo = max(nx, ny)
    t_hi = nx * ny
    if t_bounds is not None:
        t_lo = max(t_lo, t_bounds[0])
        t_hi = min(t_hi, t_bounds[1])
    if t_lo > t_hi:
        return None, None, None, dict(unsat_by_pruner=True, reason=f"empty t range [{t_lo},{t_hi}]")

    edges_T = [(i, j) for i in range(nt) for j in range(i + 1, nt) if (adj_T[i] >> j) & 1]
    deg_T = [x.bit_count() for x in adj_T]

    # Check immediate vertex degree feasibility in T: every w in T has deg_T(w) <= 7 and 6 <= deg_W(w) <= 9
    for t in range(nt):
        if deg_T[t] > 7 or deg_T[t] < nt - 23:
            return None, None, None, dict(unsat_by_pruner=True, reason=f"T vertex {t} has deg_T={deg_T[t]}")

    cnf = CompactCNF(1)
    # Primary variables:
    #   M[row][t] for row in 0..R-1, t in 0..nt-1
    #     S_rows = 0 .. c-1
    #     X_rows = c .. 5
    #     Y_rows = 6 .. 5+r
    M = [[cnf.var() for _ in range(nt)] for _ in range(R)]
    #   E_XY[ix][iy] for ix in 0..nx-1, iy in 0..ny-1
    E_XY = [[cnf.var() for _ in range(ny)] for _ in range(nx)]
    primary_max_var = cnf.nv

    S_rows = list(range(0, c))
    X_rows = list(range(c, 6))
    Y_rows = list(range(6, 6 + ny))
    A_rows = S_rows + X_rows  # |A| = 6
    B_rows = S_rows + Y_rows  # |B| = q

    # 1. Triangle-freeness with T
    for row in range(R):
        for u, v in edges_T:
            cnf.add([-M[row][u], -M[row][v]])

    # 2. Triangle-freeness across X-Y-T
    for ix, rx in enumerate(X_rows):
        for iy, ry in enumerate(Y_rows):
            exy = E_XY[ix][iy]
            for t in range(nt):
                cnf.add([-exy, -M[rx][t], -M[ry][t]])

    # 3. Mandatory X-Y saturation + t range
    all_exy = []
    for ix in range(nx):
        row_xy = [E_XY[ix][iy] for iy in range(ny)]
        all_exy.extend(row_xy)
        cnf.atleast_seq(row_xy, 1)
    for iy in range(ny):
        col_xy = [E_XY[ix][iy] for ix in range(nx)]
        cnf.atleast_seq(col_xy, 1)
    cnf.range_seq(all_exy, t_lo, t_hi)

    # 4. Exact vertex degree bounds deg_W in [6, 9] and deg_T(x), deg_T(y) <= 7
    for rs in S_rows:
        # deg_W(s) = 2 + deg_T(s) in [6, 9] => deg_T(s) in [4, 7]
        cnf.range_seq(M[rs], 4, 7)
    for ix, rx in enumerate(X_rows):
        # deg_W(x) = 1 + deg_Y(x) + deg_T(x) in [6, 9] => deg_Y(x) + deg_T(x) in [5, 8]
        # and deg_T(x) <= 7 (from alpha(H_v) <= 8)
        cnf.range_seq(M[rx] + [E_XY[ix][iy] for iy in range(ny)], 5, 8)
        cnf.atmost_seq(M[rx], 7)
    for iy, ry in enumerate(Y_rows):
        # deg_W(y) = 1 + deg_X(y) + deg_T(y) in [6, 9] => deg_X(y) + deg_T(y) in [5, 8]
        # and deg_T(y) <= 7 (from alpha(H_u) <= 8)
        cnf.range_seq(M[ry] + [E_XY[ix][iy] for ix in range(nx)], 5, 8)
        cnf.atmost_seq(M[ry], 7)

    # 5. Column degrees on T + A-domination + B-domination + ux/uy indicators + S-domination
    ux = [cnf.var() for _ in range(nt)]
    uy = [cnf.var() for _ in range(nt)]
    complete_xy = (t_lo == nx * ny)
    for t in range(nt):
        col = [M[row][t] for row in range(R)]
        lo_col = max(1, 6 - deg_T[t])
        hi_col = 9 - deg_T[t]
        cnf.range_seq(col, lo_col, hi_col)
        # Saturation with roots u (A = S U X) and v (B = S U Y)
        cnf.atleast_seq([M[row][t] for row in A_rows], 1)
        cnf.atleast_seq([M[row][t] for row in B_rows], 1)
        # ux[t] <-> OR_{x in X} M[x][t], uy[t] <-> OR_{y in Y} M[y][t]
        for rx in X_rows:
            cnf.add([-M[rx][t], ux[t]])
        cnf.add([-ux[t]] + [M[rx][t] for rx in X_rows])
        for ry in Y_rows:
            cnf.add([-M[ry][t], uy[t]])
        cnf.add([-uy[t]] + [M[ry][t] for ry in Y_rows])
        if complete_xy:
            # When G[X, Y] = K_{nx, ny}, U_X & U_Y = empty forces S-domination
            cnf.add([-ux[t], -uy[t]])
            cnf.atleast_seq([M[rs][t] for rs in S_rows], max(1, lo_col - max(nx, ny)))

    # 6. Non-edge saturation S -> T, X -> T, Y -> T
    for t in range(nt):
        nbrs = [w for w in range(nt) if (adj_T[t] >> w) & 1]
        for rs in S_rows:
            # S has no edges to X or Y, so common neighbor of s and t MUST lie in T
            cnf.add([M[rs][t]] + [M[rs][w] for w in nbrs])
        for rx in X_rows:
            # Common neighbor of x and t lies in Y (implies uy[t]) or in T
            cnf.add([M[rx][t], uy[t]] + [M[rx][w] for w in nbrs])
        for ry in Y_rows:
            # Common neighbor of y and t lies in X (implies ux[t]) or in T
            cnf.add([M[ry][t], ux[t]] + [M[ry][w] for w in nbrs])

    # 7. Pairwise codegree caps on S (codeg_W <= 9+9-11 = 7, sharing u,v => codeg_T <= 5)
    #    and nontrivial non-adjacent T-pairs
    for i in range(c):
        for j in range(i + 1, c):
            bs = []
            for t in range(nt):
                b = cnf.var()
                cnf.add([-M[S_rows[i]][t], -M[S_rows[j]][t], b])
                bs.append(b)
            cnf.atmost_seq(bs, 5)

    nontrivial_t_pairs = 0
    for u in range(nt):
        rem_u = 9 - deg_T[u]
        for v in range(u + 1, nt):
            if (adj_T[u] >> v) & 1:
                continue
            rem_v = 9 - deg_T[v]
            ct = (adj_T[u] & adj_T[v]).bit_count()
            cap_uv = 7 - ct  # worst-case deg_W(u)=deg_W(v)=9 => codeg_W <= 7
            if min(rem_u, rem_v) > cap_uv:
                nontrivial_t_pairs += 1
                bs = []
                for row in range(R):
                    b = cnf.var()
                    cnf.add([-M[row][u], -M[row][v], b])
                    bs.append(b)
                cnf.atmost_seq(bs, cap_uv)

    # 8. Exact Hall b=1 private-neighbor bounds on A (<= 4) and B (<= 10 - q)
    for ra in A_rows:
        otherA = [row for row in A_rows if row != ra]
        privA = []
        for t in range(nt):
            pa = cnf.var()
            cnf.add([-M[ra][t], pa] + [M[row][t] for row in otherA])
            privA.append(pa)
        cap_privA = 4 - (1 if (ra in S_rows and c == 1) else 0)
        cnf.atmost_seq(privA, cap_privA)

    for rb in B_rows:
        otherB = [row for row in B_rows if row != rb]
        privB = []
        for t in range(nt):
            pb = cnf.var()
            cnf.add([-M[rb][t], pb] + [M[row][t] for row in otherB])
            privB.append(pb)
        cap_privB = (10 - q) - (1 if (rb in S_rows and c == 1) else 0)
        cnf.atmost_seq(privB, cap_privB)

    # 9. Exact e(H_u) and e(H_v) edge-count bounds
    #    e(H_u) = r + eT + e(Y, T) in [118, 127]
    #    e(H_v) = nx + eT + e(X, T) in [E9[q], min(4*(39-q), (7*(39-q)+q*(10-q))//2)]
    yT_vars = [M[ry][t] for ry in Y_rows for t in range(nt)]
    xT_vars = [M[rx][t] for rx in X_rows for t in range(nt)]
    eYT_lo = max(0, 118 - r - eT)
    eYT_hi = min(len(yT_vars), 127 - r - eT)
    eHv_hi = min(4 * (39 - q), (7 * (39 - q) + q * (10 - q)) // 2)
    eXT_lo = max(0, E9[q] - nx - eT)
    eXT_hi = min(len(xT_vars), eHv_hi - nx - eT)
    if eYT_lo > eYT_hi or eXT_lo > eXT_hi:
        return None, None, None, dict(
            unsat_by_pruner=True,
            reason=f"e(H_u)/e(H_v) range empty: eYT=[{eYT_lo},{eYT_hi}], eXT=[{eXT_lo},{eXT_hi}]",
        )
    cnf.range_seq(yT_vars, eYT_lo, eYT_hi)
    cnf.range_seq(xT_vars, eXT_lo, eXT_hi)

    # 10. Static I_7(T) hitting-set constraints (100% sound!)
    i7_total = 0
    i7_encoded = 0
    if include_i7:
        I7 = enum_indep(adj_T, 7, limit=(max_i7 if max_i7 and max_i7 > 0 else None))
        i7_total = len(I7)
        i7_encoded = len(I7)
        for w in I7:
            vs = [t for t in range(nt) if (w >> t) & 1]
            ms = []
            for row in range(R):
                z = cnf.var()
                cnf.add([z] + [M[row][t] for t in vs])
                ms.append(z)
            # At most 2 of A = S U X miss W_7
            cnf.atmost_seq([ms[row] for row in A_rows], 2)
            # At most 2 of B = S U Y miss W_7
            cnf.atmost_seq([ms[row] for row in B_rows], 2)
            # At most 1 of X misses W_7 (since W_7 U R_X U {v} is independent!)
            if nx >= 2:
                cnf.atmost_seq([ms[row] for row in X_rows], 1)
            # At most 1 of Y misses W_7 (since W_7 U R_Y U {u} is independent!)
            if ny >= 2:
                cnf.atmost_seq([ms[row] for row in Y_rows], 1)

    # 11. Sound strict lex symmetry breaking within S, X, Y
    #     (No two non-adjacent vertices in a (3,10;40)-graph can have identical neighborhoods!)
    if include_lex:
        for i in range(c - 1):
            cnf.lex_lt(M[S_rows[i]], M[S_rows[i + 1]])
        for ix in range(nx - 1):
            vec1 = M[X_rows[ix]] + [E_XY[ix][iy] for iy in range(ny)]
            vec2 = M[X_rows[ix + 1]] + [E_XY[ix + 1][iy] for iy in range(ny)]
            cnf.lex_lt(vec1, vec2)
        for iy in range(ny - 1):
            vec1 = M[Y_rows[iy]] + [E_XY[ix][iy] for ix in range(nx)]
            vec2 = M[Y_rows[iy + 1]] + [E_XY[ix][iy + 1] for ix in range(nx)]
            cnf.lex_lt(vec1, vec2)

    meta = dict(
        unsat_by_pruner=False,
        branch_id=f"D6-R{r}-Q{q}",
        r=r,
        q=q,
        c=c,
        nx=nx,
        ny=ny,
        nt=nt,
        eT=eT,
        t_range=[t_lo, t_hi],
        primary_vars=primary_max_var,
        vars=cnf.nv,
        clauses=len(cnf.clauses),
        nontrivial_t_pairs=nontrivial_t_pairs,
        i7_encoded=i7_encoded,
        include_lex=include_lex,
    )
    return cnf, M, E_XY, meta


def build_40_graph(adj_T, r: int, q: int, M_rows, xy_edges):
    """Reconstruct full 40-vertex adjacency bitmask from fixed core T and (M_rows, xy_edges).

    Vertex indexing:
      0: root u (degree 6)
      1: root v (degree q), non-adjacent to 0
      2 .. 2+c-1: S
      2+c .. 7: X
      8 .. 8+r-1: Y
      8+r .. 39: T (n_T = 32 - r vertices)
    """
    c = q - r
    nx = 6 - c
    ny = r
    nt = 32 - r
    offset_T = 8 + r
    assert offset_T + nt == N_G

    g = [0] * N_G

    def add_e(u, v):
        g[u] |= 1 << v
        g[v] |= 1 << u

    for i in range(c):
        s = 2 + i
        add_e(0, s)
        add_e(1, s)
    for ix in range(nx):
        add_e(0, 2 + c + ix)
    for iy in range(ny):
        add_e(1, 8 + iy)
    for ix in range(nx):
        for iy in range(ny):
            if xy_edges[ix][iy]:
                add_e(2 + c + ix, 8 + iy)
    for i in range(nt):
        for j in range(i + 1, nt):
            if (adj_T[i] >> j) & 1:
                add_e(offset_T + i, offset_T + j)
    R = 6 + r
    for row in range(R):
        u = 2 + row
        mask = M_rows[row]
        for t in range(nt):
            if (mask >> t) & 1:
                add_e(u, offset_T + t)
    return g


def verify_ramsey_3_10_40_witness(g40):
    """Completely independent SAT witness verifier for a (3, 10; 40)-graph.

    Returns (is_valid: bool, report: dict).
    Checks:
      1. Order == 40, symmetric, loopless.
      2. Triangle-free (0 triangles).
      3. Independence number <= 9 (0 independent 10-sets via exact bitmask backtracking).
    """
    if len(g40) != N_G:
        return False, dict(error=f"Expected 40 vertices, got {len(g40)}")
    for i in range(N_G):
        if (g40[i] >> i) & 1:
            return False, dict(error=f"Self-loop at {i}")
        for j in range(i + 1, N_G):
            if ((g40[i] >> j) & 1) != ((g40[j] >> i) & 1):
                return False, dict(error=f"Asymmetric edge ({i},{j})")
            if ((g40[i] >> j) & 1) and (g40[i] & g40[j]):
                return False, dict(error=f"Triangle on edge ({i},{j})")
    i10 = enum_indep(g40, 10, limit=1)
    if i10:
        verts = [v for v in range(N_G) if (i10[0] >> v) & 1]
        return False, dict(error="Found independent 10-set", i10=verts)
    degs = [x.bit_count() for x in g40]
    return True, dict(
        status="VERIFIED_RAMSEY_3_10_40_WITNESS",
        n=N_G,
        edges=sum(degs) // 2,
        min_deg=min(degs),
        max_deg=max(degs),
        degree_counts={str(d): degs.count(d) for d in sorted(set(degs))},
    )


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def extract_cores_from_g6(g6_path: Path, expected_n: int, e_lo: int, e_hi: int, max_cores=None):
    """Stream (3, 8; expected_n) cores with edge count in [e_lo, e_hi] from a .g6 or .g6.gz file."""
    opener = gzip.open if str(g6_path).endswith(".gz") else open
    expected_len = 1 + (expected_n * (expected_n - 1) // 2 + 5) // 6
    total = 0
    selected = []
    with opener(g6_path, "rt", encoding="ascii") as fp:
        for line in fp:
            s = line.strip().removeprefix(">>graph6<<")
            if not s:
                continue
            assert len(s) == expected_len and ord(s[0]) - 63 == expected_n
            total += 1
            edges = sum((ord(ch) - 63).bit_count() for ch in s[1:])
            if e_lo <= edges <= e_hi:
                selected.append((edges, s))
                if max_cores is not None and len(selected) >= max_cores:
                    break
    return total, selected


def proof_first_solve_core(
    g6: str,
    r: int,
    q: int,
    out_dir: Path,
    seconds: int = 1200,
    t_bounds=None,
    include_i7: bool = True,
    max_i7: int = 2000,
):
    """Proof-first single-pass Kissat + drat-trim (-L LRAT) + lrat-check loop for one fixed core."""
    out_dir.mkdir(parents=True, exist_ok=True)
    nt = 32 - r
    c = q - r
    nx = 6 - c
    ny = r
    R = 6 + r
    offset_T = 8 + r

    adj_T = decode_g6(g6, expected_n=nt)
    cnf, M, E_XY, meta = build_d6_core_cnf(
        adj_T, r=r, q=q, t_bounds=t_bounds, include_i7=include_i7, max_i7=max_i7, include_lex=True
    )
    if meta.get("unsat_by_pruner"):
        report = dict(g6=g6, branch_id=f"D6-R{r}-Q{q}", status="CERTIFIED_UNSAT_PRUNER", meta=meta)
        (out_dir / "result.json").write_text(json.dumps(report, indent=2) + "\n")
        return report

    extra_cuts = []
    seen_cuts = set()
    t0 = time.monotonic()
    iters = 0
    report = dict(g6=g6, branch_id=f"D6-R{r}-Q{q}", meta=meta, status="OPEN", iters=0, cuts=0)
    primary_max = meta["primary_vars"]

    while time.monotonic() - t0 < seconds:
        iters += 1
        rem_sec = max(5, int(seconds - (time.monotonic() - t0)))
        cnf_path = out_dir / "leaf.cnf"
        drat_path = out_dir / "leaf.drat"
        lrat_path = out_dir / "leaf.lrat"
        cnf.write_dimacs(cnf_path, extra_cuts)

        def cap_fsize():
            resource.setrlimit(resource.RLIMIT_FSIZE, (1024 * 1024**2, 1024 * 1024**2))

        t_solve0 = time.monotonic()
        with open(out_dir / "kissat.log", "w") as log:
            proc = subprocess.run(
                ["kissat", f"--time={rem_sec}", str(cnf_path), str(drat_path)],
                stdout=log,
                stderr=subprocess.STDOUT,
                timeout=rem_sec + 30,
                preexec_fn=cap_fsize,
            )
        solve_sec = time.monotonic() - t_solve0

        if proc.returncode == 20:
            cnf_sha = sha256_file(cnf_path)
            drat_sha = sha256_file(drat_path)
            t_ver0 = time.monotonic()
            with open(out_dir / "drat-trim.log", "w") as log:
                v = subprocess.run(
                    ["drat-trim", str(cnf_path), str(drat_path), "-L", str(lrat_path)],
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    timeout=max(60, rem_sec),
                )
            ok_drat = (
                v.returncode == 0
                and "s VERIFIED" in (out_dir / "drat-trim.log").read_text(errors="replace")
            )
            ok_lrat = False
            lrat_sha = None
            if ok_drat and lrat_path.exists() and shutil.which("lrat-check"):
                with open(out_dir / "lrat-check.log", "w") as log:
                    lv = subprocess.run(
                        ["lrat-check", str(cnf_path), str(lrat_path)],
                        stdout=log,
                        stderr=subprocess.STDOUT,
                        timeout=max(60, rem_sec),
                    )
                ok_lrat = (
                    lv.returncode == 0
                    and "s VERIFIED" in (out_dir / "lrat-check.log").read_text(errors="replace")
                )
                if ok_lrat:
                    lrat_sha = sha256_file(lrat_path)
                    with open(lrat_path, "rb") as fi, gzip.open(
                        out_dir / "leaf.lrat.gz", "wb", compresslevel=1
                    ) as fo:
                        shutil.copyfileobj(fi, fo)
            ver_sec = time.monotonic() - t_ver0
            if ok_drat:
                if not ok_lrat:
                    with open(drat_path, "rb") as fi, gzip.open(
                        out_dir / "leaf.drat.gz", "wb", compresslevel=1
                    ) as fo:
                        shutil.copyfileobj(fi, fo)
                report.update(
                    status="CERTIFIED_UNSAT",
                    iters=iters,
                    cuts=len(extra_cuts),
                    cnf_sha256=cnf_sha,
                    drat_sha256=drat_sha,
                    lrat_verified=ok_lrat,
                    lrat_sha256=lrat_sha,
                    solve_seconds=round(solve_sec, 3),
                    verify_seconds=round(ver_sec, 3),
                )
            else:
                report.update(status="UNSAT_VERIFICATION_FAILED", iters=iters, cuts=len(extra_cuts))
            drat_path.unlink(missing_ok=True)
            lrat_path.unlink(missing_ok=True)
            cnf_path.unlink(missing_ok=True)
            break

        elif proc.returncode == 10:
            drat_path.unlink(missing_ok=True)
            vals = set()
            for line in (out_dir / "kissat.log").read_text(errors="replace").splitlines():
                if line.startswith("v "):
                    for tok in line.split()[1:]:
                        lit = int(tok)
                        if 0 < lit <= primary_max:
                            vals.add(lit)
            M_rows = [
                sum((1 << t) for t in range(nt) if M[row][t] in vals) for row in range(R)
            ]
            xy_edges = [
                [1 if E_XY[ix][iy] in vals else 0 for iy in range(ny)] for ix in range(nx)
            ]
            g40 = build_40_graph(adj_T, r, q, M_rows, xy_edges)
            i10s = enum_indep(g40, 10, limit=128)
            if not i10s:
                ok_wit, wit_rep = verify_ramsey_3_10_40_witness(g40)
                assert ok_wit, f"Witness verification failed: {wit_rep}"
                (out_dir / "witness.txt").write_text(
                    "".join(
                        "".join(str((g40[i] >> j) & 1) for j in range(N_G)) + "\n"
                        for i in range(N_G)
                    )
                )
                (out_dir / "witness_verified.json").write_text(json.dumps(wit_rep, indent=2) + "\n")
                report.update(
                    status="VERIFIED_WITNESS",
                    iters=iters,
                    cuts=len(extra_cuts),
                    witness_report=wit_rep,
                )
                break

            added = 0
            for mask in i10s:
                rs = tuple(v - 2 for v in range(2, 2 + R) if (mask >> v) & 1)
                ts = tuple(v - offset_T for v in range(offset_T, N_G) if (mask >> v) & 1)
                xs = [row - c for row in rs if c <= row < 6]
                ys = [row - 6 for row in rs if 6 <= row < 6 + ny]
                cl = [M[row][t] for row in rs for t in ts] + [
                    E_XY[ix][iy] for ix in xs for iy in ys
                ]
                key = tuple(sorted(set(cl)))
                assert key, "Empty I10 cut!"
                if key not in seen_cuts:
                    seen_cuts.add(key)
                    extra_cuts.append(list(key))
                    added += 1
            assert added > 0
            report.update(iters=iters, cuts=len(extra_cuts))

        else:
            drat_path.unlink(missing_ok=True)
            report.update(
                status="OPEN_TIMEOUT",
                kissat_exit=proc.returncode,
                iters=iters,
                cuts=len(extra_cuts),
            )
            break

    report["total_seconds"] = round(time.monotonic() - t0, 3)
    (out_dir / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report), flush=True)
    return report


def main():
    ap = argparse.ArgumentParser(description="Tier-1 D6 Fixed-Core Compact CNF Solver")
    ap.add_argument("--g6", required=True, help="graph6 string of (3, 8; 32-r) core T")
    ap.add_argument("--r", type=int, required=True, choices=[5, 6, 7])
    ap.add_argument("--q", type=int, required=True, choices=[6, 7, 8, 9])
    ap.add_argument("--out", type=Path, default=Path("out_d6_core"))
    ap.add_argument("--seconds", type=int, default=1200)
    ap.add_argument("--t-lo", type=int, default=None)
    ap.add_argument("--t-hi", type=int, default=None)
    ap.add_argument("--no-i7", action="store_true")
    ap.add_argument("--max-i7", type=int, default=2000)
    a = ap.parse_args()
    tb = (a.t_lo, a.t_hi) if (a.t_lo is not None and a.t_hi is not None) else None
    proof_first_solve_core(
        a.g6,
        r=a.r,
        q=a.q,
        out_dir=a.out,
        seconds=a.seconds,
        t_bounds=tb,
        include_i7=(not a.no_i7),
        max_i7=a.max_i7,
    )


if __name__ == "__main__":
    main()
