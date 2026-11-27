#!/usr/bin/env python3
r"""Unified compact CNF encoder + single-pass Proof-First Kissat + drat-trim + lrat-check
solver for Ramsey R(3,10) D9 cases c in {3, 4, 5} (also supports c in {6, 7}).

Supports TWO modes:
  - Mode A (Free-T Skeleton-Locked Compact CNF — Primary for C5/C4/C3):
      Fixes roots {0, 1}, S (size c), X (size 9-c), Y (size 9-c), and a canonical
      bipartite skeleton H = G[X, Y]. Encodes G[S u X u Y, T] + G[T] with exact
      degrees, triangle-freeness, S-domination, pairwise codegrees <= c, Hall b=1,
      lazy universal T-pair codegree cuts (zero redundant T-pair counters!), and
      sound lex symmetry breaking on S and T.
  - Mode B (Fixed-Core T Compact CNF — Direct generalization of d9c7_compact_cnf.py):
      Given a fixed (3,8; n_T, e_T) graph6 core T and compatible skeleton H, collapses
      to the (18-c) x (20+c) Boolean matrix M[r][t] with exact S-domination, zero
      redundant T-pair codegree counters, static I7(T) hitting-set clauses, Hall b=1,
      and single-pass Proof-First Kissat + drat-trim (-L LRAT) + lrat-check.

Every SAT candidate is checked by an independent full 40-vertex graph verifier
(9-regularity, triangle-freeness, alpha(G) <= 9, global max non-edge codegree == c,
and exact skeleton match).
"""
import argparse
import gzip
import hashlib
import itertools
import json
import os
import random
import resource
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import d9c345_pruner as pruner

N_G = 40


def decode_g6(raw: str, expected_n: int = None):
    s = raw.strip().removeprefix('>>graph6<<')
    n = ord(s[0]) - 63
    if expected_n is not None:
        assert n == expected_n, f"Expected {expected_n} vertices, got {n}"
    assert len(s) == 1 + (n * (n - 1) // 2 + 5) // 6, f"Bad graph6 length for n={n}"
    adj = [0] * n
    k = 0
    for j in range(n):
        for i in range(j):
            if ((ord(s[1 + k // 6]) - 63) >> (5 - k % 6)) & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return adj


def encode_g6(adj) -> str:
    n = len(adj)
    out = [chr(n + 63)]
    bits = []
    for j in range(n):
        for i in range(j):
            bits.append((adj[i] >> j) & 1)
    while len(bits) % 6:
        bits.append(0)
    for k in range(0, len(bits), 6):
        val = 0
        for b in bits[k:k + 6]:
            val = (val << 1) | b
        out.append(chr(val + 63))
    return ''.join(out)


def enum_indep(adj, k: int, limit=None, verts=None, rng=None):
    n = len(adj)
    if verts is None:
        order = list(range(n))
    else:
        order = list(verts)
    if rng is not None:
        rng.shuffle(order)
    m = len(order)
    inv = {v: i for i, v in enumerate(order)}
    loc_adj = [0] * m
    for i, u in enumerate(order):
        mask = 0
        a = adj[u]
        while a:
            b = a & -a
            v = b.bit_length() - 1
            a ^= b
            if v in inv:
                mask |= 1 << inv[v]
        loc_adj[i] = mask

    res = []

    def dfs(cand: int, rem: int, cur_mask: int):
        if limit is not None and len(res) >= limit:
            return
        if rem == 0:
            res.append(cur_mask)
            return
        while cand.bit_count() >= rem:
            if limit is not None and len(res) >= limit:
                return
            b = cand & -cand
            i = b.bit_length() - 1
            cand ^= b
            dfs(cand & ~loc_adj[i], rem - 1, cur_mask | (1 << order[i]))

    dfs((1 << m) - 1, k, 0)
    return res


def verify_r38_core(adj, n_T: int, expected_edges: int = None):
    assert len(adj) == n_T, f"Expected {n_T} vertices, got {len(adj)}"
    edges = sum(x.bit_count() for x in adj) // 2
    if expected_edges is not None:
        assert edges == expected_edges, f"Expected {expected_edges} edges, got {edges}"
    for i in range(n_T):
        assert not ((adj[i] >> i) & 1), "Self-loop"
        for j in range(i + 1, n_T):
            assert ((adj[i] >> j) & 1) == ((adj[j] >> i) & 1), "Asymmetric adjacency"
            if (adj[i] >> j) & 1:
                assert (adj[i] & adj[j]) == 0, f"Triangle on ({i},{j})"
    assert len(enum_indep(adj, 8, limit=1)) == 0, "Core has an independent 8-set"
    return edges


def max_xy_indep_size(rows, c: int) -> int:
    """Maximum |I_X| + |I_Y| over independent sets I_X u I_Y of H = G[X, Y]
    with |I_X| <= c and |I_Y| <= c."""
    nX = len(rows)
    fullY = (1 << nX) - 1
    best = 0
    for ix in range(1 << nX):
        a = ix.bit_count()
        if a > c:
            continue
        forbY = 0
        for i in range(nX):
            if (ix >> i) & 1:
                forbY |= rows[i]
        b = min(c, (fullY ^ forbY).bit_count())
        if a + b > best:
            best = a + b
    return best


class CompactCNF:
    def __init__(self, start_var: int = 1):
        self.nv = start_var - 1
        self.clauses = []

    def var(self) -> int:
        self.nv += 1
        return self.nv

    def add(self, cl):
        self.clauses.append(list(cl))

    def atmost_seq(self, xs, k: int):
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

    def atleast_seq(self, xs, k: int):
        self.atmost_seq([-x for x in xs], len(xs) - k)

    def exact_seq(self, xs, k: int):
        self.atmost_seq(xs, k)
        self.atleast_seq(xs, k)

    def bounds_seq(self, xs, lo: int, hi: int):
        self.atmost_seq(xs, hi)
        self.atleast_seq(xs, lo)

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

    def lex_le(self, a, b):
        """Enforce bitvector a <= b (MSB at index 0)."""
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

    def write_dimacs(self, path: Path, extra_clauses=()):
        total = len(self.clauses) + len(extra_clauses)
        with open(path, 'w') as f:
            f.write(f"p cnf {self.nv} {total}\n")
            for cl in self.clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')
            for cl in extra_clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')


def build_d9c345_cnf(c: int, skeleton_rows, adj_T=None, include_i7: bool = True, include_lex: bool = True):
    """Build compact DIMACS CNF for D9-C{c} with fixed bipartite skeleton H = skeleton_rows.
    If adj_T is None: Free-T mode (Mode A).
    If adj_T is provided: Fixed-Core mode (Mode B).
    """
    assert c in (3, 4, 5, 6, 7), f"Unsupported c={c}"
    nX = 9 - c
    nT = 20 + c
    R = 18 - c  # |S| + |X| + |Y| = c + 2*(9 - c)
    assert len(skeleton_rows) == nX
    cols = pruner.rows_to_cols(skeleton_rows, nX)
    exy = sum(r.bit_count() for r in skeleton_rows)
    eT_expected = 18 + 9 * c + exy
    alpha_xy = max_xy_indep_size(skeleton_rows, c)
    is_complete_H = (exy == nX * nX)

    if adj_T is not None:
        verify_r38_core(adj_T, nT, expected_edges=eT_expected)

    cnf = CompactCNF(1)
    # Primary cross variables: M[r][t] for r in 0..R-1, t in 0..nT-1
    # Row layout: 0..c-1 = S, c..8 = X, 9..17-c = Y
    M = [[cnf.var() for _ in range(nT)] for _ in range(R)]

    # T-edge variables (only in Free-T mode)
    ET_var = {}
    if adj_T is None:
        for u in range(nT):
            for v in range(u + 1, nT):
                var = cnf.var()
                ET_var[(u, v)] = var
                ET_var[(v, u)] = var

    A_rows = list(range(9))                         # S u X
    B_rows = list(range(c)) + list(range(9, R))     # S u Y
    S_rows = list(range(c))
    X_rows = list(range(c, 9))
    Y_rows = list(range(9, R))

    # 1. Triangle-free constraints
    if adj_T is None:
        # Inside T
        for u, v, w in itertools.combinations(range(nT), 3):
            cnf.add([-ET_var[(u, v)], -ET_var[(u, w)], -ET_var[(v, w)]])
        # Between S u X u Y and T
        for r in range(R):
            for u in range(nT):
                for v in range(u + 1, nT):
                    cnf.add([-ET_var[(u, v)], -M[r][u], -M[r][v]])
    else:
        t_edges = [(u, v) for u in range(nT) for v in range(u + 1, nT) if (adj_T[u] >> v) & 1]
        for r in range(R):
            for u, v in t_edges:
                cnf.add([-M[r][u], -M[r][v]])

    # Triangle-free across H = G[X, Y]
    for i in range(nX):
        for j in range(nX):
            if (skeleton_rows[i] >> j) & 1:
                rx = X_rows[i]
                ry = Y_rows[j]
                for t in range(nT):
                    cnf.add([-M[rx][t], -M[ry][t]])

    # 2. Exact row degrees into T
    for r in S_rows:
        cnf.exact_seq(M[r], 7)
    for i, r in enumerate(X_rows):
        cnf.exact_seq(M[r], 8 - skeleton_rows[i].bit_count())
    for j, r in enumerate(Y_rows):
        cnf.exact_seq(M[r], 8 - cols[j].bit_count())

    # 3. Column degrees, T-degree bounds, A/B codegree bounds, and S-domination
    min_dt = max(0, c - 3)
    if adj_T is None:
        for t in range(nT):
            t_nbrs = [ET_var[(t, u)] for u in range(nT) if u != t]
            cnf.exact_seq([M[r][t] for r in range(R)] + t_nbrs, 9)
            cnf.bounds_seq(t_nbrs, min_dt, 7)
            cnf.bounds_seq([M[r][t] for r in A_rows], 1, c)
            cnf.bounds_seq([M[r][t] for r in B_rows], 1, c)
            if is_complete_H:
                cnf.atleast_seq([M[r][t] for r in S_rows], 1)
    else:
        deg_T = [x.bit_count() for x in adj_T]
        rem_T = [9 - d for d in deg_T]
        for t in range(nT):
            cnf.exact_seq([M[r][t] for r in range(R)], rem_T[t])
            cnf.bounds_seq([M[r][t] for r in A_rows], 1, c)
            cnf.bounds_seq([M[r][t] for r in B_rows], 1, c)
            # Exact S-domination lower bound: d_S(t) >= rem_T[t] - alpha_xy (and >= 1 if complete H)
            min_ds = max(1 if is_complete_H else 0, rem_T[t] - alpha_xy)
            if min_ds > 0:
                cnf.atleast_seq([M[r][t] for r in S_rows], min_ds)

    # 4. Pairwise codegree caps (<= c) on S, X, Y
    def add_pair_cap(r1: int, r2: int, cap: int, require_atleast_one: bool = False):
        if cap < 0:
            cnf.add([])
            return
        if cap == 0:
            if require_atleast_one:
                cnf.add([])
                return
            for t in range(nT):
                cnf.add([-M[r1][t], -M[r2][t]])
            return
        bs = []
        for t in range(nT):
            b = cnf.var()
            cnf.add([-M[r1][t], -M[r2][t], b])
            if require_atleast_one:
                cnf.add([-b, M[r1][t]])
                cnf.add([-b, M[r2][t]])
            bs.append(b)
        cnf.atmost_seq(bs, cap)
        if require_atleast_one:
            cnf.add(bs)

    # S-S pairs: share u, v -> codeg_T <= c - 2
    for i in range(c):
        for j in range(i + 1, c):
            add_pair_cap(S_rows[i], S_rows[j], c - 2)
    # S-X and S-Y pairs: share u (or v) -> codeg_T <= c - 1
    for s in S_rows:
        for x in X_rows:
            add_pair_cap(s, x, c - 1)
        for y in Y_rows:
            add_pair_cap(s, y, c - 1)
    # X-X pairs: share u + |N_Y(x1) & N_Y(x2)|
    for i in range(nX):
        for j in range(i + 1, nX):
            cap = c - 1 - (skeleton_rows[i] & skeleton_rows[j]).bit_count()
            add_pair_cap(X_rows[i], X_rows[j], cap)
    # Y-Y pairs: share v + |N_X(y1) & N_X(y2)|
    for i in range(nX):
        for j in range(i + 1, nX):
            cap = c - 1 - (cols[i] & cols[j]).bit_count()
            add_pair_cap(Y_rows[i], Y_rows[j], cap)
    # X-Y non-edges: common neighbors exist ONLY in T -> 1 <= codeg_T(x, y) <= c
    for i in range(nX):
        for j in range(nX):
            if not ((skeleton_rows[i] >> j) & 1):
                add_pair_cap(X_rows[i], Y_rows[j], c, require_atleast_one=True)

    # 5. Zero redundant T-pair codegree counters!
    nontrivial_t_pairs = 0
    if adj_T is not None:
        deg_T = [x.bit_count() for x in adj_T]
        rem_T = [9 - d for d in deg_T]
        for u in range(nT):
            for v in range(u + 1, nT):
                if (adj_T[u] >> v) & 1:
                    continue
                ct = (adj_T[u] & adj_T[v]).bit_count()
                cap = c - ct
                if min(rem_T[u], rem_T[v]) > cap:
                    nontrivial_t_pairs += 1
                    if cap == 0:
                        for r in range(R):
                            cnf.add([-M[r][u], -M[r][v]])
                    else:
                        bs = []
                        for r in range(R):
                            b = cnf.var()
                            cnf.add([-M[r][u], -M[r][v], b])
                            bs.append(b)
                        cnf.atmost_seq(bs, cap)

    # 6. Hall b=1 private-neighbor caps on A = S u X and B = S u Y
    for r in S_rows:
        otherA = [q for q in A_rows if q != r]
        otherB = [q for q in B_rows if q != r]
        privA, privB = [], []
        for t in range(nT):
            pa = cnf.var()
            cnf.add([-M[r][t], pa] + [M[q][t] for q in otherA])
            privA.append(pa)
            pb = cnf.var()
            cnf.add([-M[r][t], pb] + [M[q][t] for q in otherB])
            privB.append(pb)
        cnf.atmost_seq(privA, 1)
        cnf.atmost_seq(privB, 1)

    for i, r in enumerate(X_rows):
        used_in_Y = sum(1 for j in range(nX) if cols[j] == (1 << i))
        cap = 1 - used_in_Y
        otherA = [q for q in A_rows if q != r]
        privA = []
        for t in range(nT):
            pa = cnf.var()
            cnf.add([-M[r][t], pa] + [M[q][t] for q in otherA])
            privA.append(pa)
        cnf.atmost_seq(privA, cap)

    for j, r in enumerate(Y_rows):
        used_in_X = sum(1 for i in range(nX) if skeleton_rows[i] == (1 << j))
        cap = 1 - used_in_X
        otherB = [q for q in B_rows if q != r]
        privB = []
        for t in range(nT):
            pb = cnf.var()
            cnf.add([-M[r][t], pb] + [M[q][t] for q in otherB])
            privB.append(pb)
        cnf.atmost_seq(privB, cap)

    # 7. Static I7(T) hitting-set clauses (in Fixed-Core mode)
    i7_count = 0
    if adj_T is not None and include_i7:
        I7 = enum_indep(adj_T, 7)
        i7_count = len(I7)
        for w in I7:
            vs = [t for t in range(nT) if (w >> t) & 1]
            ms = []
            for r in range(R):
                z = cnf.var()
                cnf.add([z] + [M[r][t] for t in vs])
                ms.append(z)
            cnf.atmost_seq([ms[r] for r in A_rows], 2)
            cnf.atmost_seq([ms[r] for r in B_rows], 2)

    # 8. Sound lex symmetry breaking
    if include_lex:
        # Rows of S have degree 7 > c - 2 (max S-S codegree), so all S rows are distinct -> strict lex_lt is 100% sound!
        for i in range(c - 1):
            cnf.lex_lt(M[S_rows[i]], M[S_rows[i + 1]])
        # In Free-T mode, vertices of T are completely symmetric -> sort T columns by M[:][t] (lex_le)
        if adj_T is None:
            for t in range(nT - 1):
                cnf.lex_le([M[r][t] for r in range(R)], [M[r][t + 1] for r in range(R)])

    meta = {
        'c': c,
        'nX': nX,
        'nT': nT,
        'R': R,
        'e_xy': exy,
        'e_T': eT_expected,
        'mode': 'free_T' if adj_T is None else 'fixed_core',
        'vars': cnf.nv,
        'clauses': len(cnf.clauses),
        'nontrivial_t_pairs': nontrivial_t_pairs,
        'i7_count': i7_count,
        'include_lex': include_lex,
    }
    return cnf, M, ET_var, meta


def model_to_40_graph(c: int, skeleton_rows, pos_lits: set, M, ET_var, adj_T=None):
    nX = 9 - c
    nT = 20 + c
    R = 18 - c
    g = [0] * N_G

    def add_e(u, v):
        g[u] |= 1 << v
        g[v] |= 1 << u

    # Roots 0, 1 to S, X, Y
    for s in range(2, 2 + c):
        add_e(0, s)
        add_e(1, s)
    for x in range(2 + c, 11):
        add_e(0, x)
    for y in range(11, 20 - c):
        add_e(1, y)
    # Skeleton H = G[X, Y]
    for i in range(nX):
        for j in range(nX):
            if (skeleton_rows[i] >> j) & 1:
                add_e(2 + c + i, 11 + j)
    # Cross edges M[r][t]
    t_off = 20 - c
    for r in range(R):
        u = 2 + r
        for t in range(nT):
            if M[r][t] in pos_lits:
                add_e(u, t_off + t)
    # T internal edges
    if adj_T is not None:
        for u in range(nT):
            for v in range(u + 1, nT):
                if (adj_T[u] >> v) & 1:
                    add_e(t_off + u, t_off + v)
    else:
        for u in range(nT):
            for v in range(u + 1, nT):
                if ET_var[(u, v)] in pos_lits:
                    add_e(t_off + u, t_off + v)
    return g


def verify_40_witness(g, c: int, skeleton_rows=None, check_alpha: bool = True):
    """Independent full 40-vertex Ramsey (3,10) D9-C{c} witness verifier.
    Returns (is_valid, reason).
    """
    if len(g) != N_G:
        return False, f"wrong_order:{len(g)}"
    for u in range(N_G):
        if (g[u] >> u) & 1:
            return False, f"self_loop:{u}"
        if g[u].bit_count() != 9:
            return False, f"non_9_regular:{u}:{g[u].bit_count()}"
        for v in range(u + 1, N_G):
            if ((g[u] >> v) & 1) != ((g[v] >> u) & 1):
                return False, f"asymmetric:{u},{v}"
            if (g[u] >> v) & 1:
                if g[u] & g[v]:
                    return False, f"triangle:{u},{v}"
    if (g[0] >> 1) & 1:
        return False, "roots_adjacent"
    if (g[0] & g[1]).bit_count() != c:
        return False, f"root_codeg:{(g[0] & g[1]).bit_count()}!={c}"
    max_codeg = 0
    for u in range(N_G):
        for v in range(u + 1, N_G):
            if not ((g[u] >> v) & 1):
                cg = (g[u] & g[v]).bit_count()
                if cg == 0:
                    return False, f"zero_codeg:{u},{v}"
                if cg > max_codeg:
                    max_codeg = cg
    if max_codeg != c:
        return False, f"max_codeg:{max_codeg}!={c}"
    if skeleton_rows is not None:
        nX = 9 - c
        for i in range(nX):
            for j in range(nX):
                want = (skeleton_rows[i] >> j) & 1
                got = (g[2 + c + i] >> (11 + j)) & 1
                if want != got:
                    return False, f"skeleton_mismatch:{i},{j}"
    if check_alpha:
        if enum_indep(g, 10, limit=1):
            return False, "has_I10"
    return True, "VALID_R310_D9_WITNESS"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def edge_var_lookup(u: int, v: int, c: int, M, ET_var):
    """Return CNF variable for edge (u, v) if unfixed, or None if fixed."""
    if u > v:
        u, v = v, u
    t_off = 20 - c
    if u >= t_off and v >= t_off:
        return ET_var.get((u - t_off, v - t_off), None)
    if 2 <= u < t_off and v >= t_off:
        return M[u - 2][v - t_off]
    return None


def proof_first_solve(c: int, skeleton_rows, out_dir: Path, seconds: int = 600,
                      adj_T=None, include_i7: bool = True, include_lex: bool = True,
                      orbit_id: str = None):
    """Single-pass Proof-First Kissat + drat-trim (-L LRAT) + lrat-check CEGAR loop."""
    out_dir.mkdir(parents=True, exist_ok=True)
    cnf, M, ET_var, meta = build_d9c345_cnf(
        c, skeleton_rows, adj_T=adj_T, include_i7=include_i7, include_lex=include_lex
    )
    nT = 20 + c
    t_off = 20 - c
    S = list(range(2, 2 + c))
    X = list(range(2 + c, 11))
    Y = list(range(11, 20 - c))
    T = list(range(t_off, N_G))
    H0 = [1] + Y + T
    H1 = [0] + X + T

    extra_cuts = []
    seen_cuts = set()
    rng = random.Random(310345 + c * 10007 + sum(r << (6 * i) for i, r in enumerate(skeleton_rows)))
    t0 = time.monotonic()
    iters = 0
    codeg_cuts = 0
    i10_cuts = 0

    report = {
        'orbit_id': orbit_id or f"D9-C{c}-custom",
        'c': c,
        'rows': list(skeleton_rows),
        'meta': meta,
        'status': 'OPEN',
        'iters': 0,
        'codeg_cuts': 0,
        'i10_cuts': 0,
        'cuts': 0,
    }

    while time.monotonic() - t0 < seconds:
        iters += 1
        rem_sec = max(5, int(seconds - (time.monotonic() - t0)))
        cnf_path = out_dir / 'leaf.cnf'
        drat_path = out_dir / 'leaf.drat'
        lrat_path = out_dir / 'leaf.lrat'
        cnf.write_dimacs(cnf_path, extra_cuts)

        def cap_fsize():
            resource.setrlimit(resource.RLIMIT_FSIZE, (1024 * 1024 ** 2, 1024 * 1024 ** 2))

        t_solve0 = time.monotonic()
        with open(out_dir / 'kissat.log', 'w') as log:
            r = subprocess.run(
                ['kissat', f'--time={rem_sec}', str(cnf_path), str(drat_path)],
                stdout=log, stderr=subprocess.STDOUT, timeout=rem_sec + 30, preexec_fn=cap_fsize
            )
        solve_sec = time.monotonic() - t_solve0

        if r.returncode == 20:
            cnf_sha = sha256_file(cnf_path)
            drat_sha = sha256_file(drat_path)
            t_ver0 = time.monotonic()
            with open(out_dir / 'drat-trim.log', 'w') as log:
                v = subprocess.run(
                    ['drat-trim', str(cnf_path), str(drat_path), '-L', str(lrat_path)],
                    stdout=log, stderr=subprocess.STDOUT, timeout=max(60, rem_sec)
                )
            ok_drat = (v.returncode == 0 and 's VERIFIED' in (out_dir / 'drat-trim.log').read_text(errors='replace'))
            ok_lrat = False
            lrat_sha = None
            if ok_drat and lrat_path.exists() and shutil.which('lrat-check'):
                with open(out_dir / 'lrat-check.log', 'w') as log:
                    lv = subprocess.run(
                        ['lrat-check', str(cnf_path), str(lrat_path)],
                        stdout=log, stderr=subprocess.STDOUT, timeout=max(60, rem_sec)
                    )
                ok_lrat = (lv.returncode == 0 and 's VERIFIED' in (out_dir / 'lrat-check.log').read_text(errors='replace'))
                if ok_lrat:
                    lrat_sha = sha256_file(lrat_path)
                    with open(lrat_path, 'rb') as fi, gzip.open(out_dir / 'leaf.lrat.gz', 'wb', compresslevel=1) as fo:
                        shutil.copyfileobj(fi, fo)
            ver_sec = time.monotonic() - t_ver0
            if ok_drat:
                with open(drat_path, 'rb') as fi, gzip.open(out_dir / 'leaf.drat.gz', 'wb', compresslevel=1) as fo:
                    shutil.copyfileobj(fi, fo)
                report.update(
                    status='CERTIFIED_UNSAT', iters=iters, codeg_cuts=codeg_cuts,
                    i10_cuts=i10_cuts, cuts=len(extra_cuts),
                    cnf_sha256=cnf_sha, drat_sha256=drat_sha, lrat_verified=ok_lrat,
                    lrat_sha256=lrat_sha, solve_seconds=round(solve_sec, 3), verify_seconds=round(ver_sec, 3),
                )
            else:
                report.update(status='UNSAT_VERIFICATION_FAILED', iters=iters, cuts=len(extra_cuts))
            drat_path.unlink(missing_ok=True)
            lrat_path.unlink(missing_ok=True)
            cnf_path.unlink(missing_ok=True)
            break

        elif r.returncode == 10:
            drat_path.unlink(missing_ok=True)
            pos_lits = set()
            for line in (out_dir / 'kissat.log').read_text(errors='replace').splitlines():
                if line.startswith('v '):
                    for tok in line.split()[1:]:
                        lit = int(tok)
                        if lit > 0:
                            pos_lits.add(lit)
            g40 = model_to_40_graph(c, skeleton_rows, pos_lits, M, ET_var, adj_T=adj_T)
            added = 0

            # 1. Lazy universal T-pair codegree > c cuts (zero auxiliary vars!)
            if adj_T is None:
                for u in T:
                    for v in T:
                        if u >= v or ((g40[u] >> v) & 1):
                            continue
                        common = g40[u] & g40[v]
                        if common.bit_count() > c:
                            ws = [w for w in range(N_G) if (common >> w) & 1][:c + 1]
                            cl = [ET_var[(u - t_off, v - t_off)]]
                            for w in ws:
                                vu = edge_var_lookup(u, w, c, M, ET_var)
                                vv = edge_var_lookup(v, w, c, M, ET_var)
                                if vu is not None:
                                    cl.append(-vu)
                                if vv is not None:
                                    cl.append(-vv)
                            key = ('cg', tuple(sorted(cl)))
                            if key not in seen_cuts:
                                seen_cuts.add(key)
                                extra_cuts.append(cl)
                                codeg_cuts += 1
                                added += 1

            # 2. Fast structural I8(T), I9(H0), I9(H1), and general I10(G) universal cuts
            bad_i10 = set()
            for verts, k2, prefix, lim in ((T, 8, (0, 1), 128), (H0, 9, (0,), 128), (H1, 9, (1,), 128), (range(N_G), 10, (), 256)):
                for mask in enum_indep(g40, k2, limit=lim, verts=verts, rng=rng):
                    full_mask = mask
                    for pv in prefix:
                        full_mask |= 1 << pv
                    bad_i10.add(full_mask)

            for mask in sorted(bad_i10):
                vs = [v for v in range(N_G) if (mask >> v) & 1]
                cl = []
                for a, b in itertools.combinations(vs, 2):
                    ev = edge_var_lookup(a, b, c, M, ET_var)
                    if ev is not None:
                        cl.append(ev)
                key = ('i10', tuple(sorted(cl)))
                if key not in seen_cuts:
                    seen_cuts.add(key)
                    assert cl, "Empty I10 cut!"
                    extra_cuts.append(cl)
                    i10_cuts += 1
                    added += 1

            if added == 0:
                ok, reason = verify_40_witness(g40, c, skeleton_rows=skeleton_rows, check_alpha=True)
                assert ok, f"Model had 0 cuts but failed witness verification: {reason}"
                (out_dir / 'witness.txt').write_text(
                    ''.join(''.join(str((g40[i] >> j) & 1) for j in range(N_G)) + '\n' for i in range(N_G))
                )
                report.update(
                    status='VERIFIED_WITNESS', iters=iters, codeg_cuts=codeg_cuts,
                    i10_cuts=i10_cuts, cuts=len(extra_cuts),
                )
                break

            report.update(iters=iters, codeg_cuts=codeg_cuts, i10_cuts=i10_cuts, cuts=len(extra_cuts))
        else:
            drat_path.unlink(missing_ok=True)
            report.update(status='OPEN_TIMEOUT', kissat_exit=r.returncode, iters=iters, cuts=len(extra_cuts))
            break

    report['total_seconds'] = round(time.monotonic() - t0, 3)
    (out_dir / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)
    return report


def main():
    ap = argparse.ArgumentParser(description='Unified compact CNF & Proof-First Kissat solver for D9-C3/C4/C5')
    ap.add_argument('--c', type=int, required=True, choices=[3, 4, 5, 6, 7])
    ap.add_argument('--rows', required=True, help='JSON list of skeleton row bitmasks (length 9-c)')
    ap.add_argument('--core-g6', default=None, help='Optional fixed (3,8; n_T) graph6 core string')
    ap.add_argument('--out', type=Path, default=Path('out_cnf'))
    ap.add_argument('--seconds', type=int, default=600)
    ap.add_argument('--orbit-id', default=None)
    ap.add_argument('--no-i7', action='store_true')
    ap.add_argument('--no-lex', action='store_true')
    args = ap.parse_args()

    rows = json.loads(args.rows)
    adj_T = decode_g6(args.core_g6, expected_n=20 + args.c) if args.core_g6 else None
    proof_first_solve(
        args.c, rows, args.out, seconds=args.seconds, adj_T=adj_T,
        include_i7=not args.no_i7, include_lex=not args.no_lex, orbit_id=args.orbit_id
    )


if __name__ == '__main__':
    main()
