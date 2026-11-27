#!/usr/bin/env python3
"""Compact Fixed-(3,8; n_T)-Core DIMACS CNF Encoder, Proof-First Kissat/DRAT/LRAT Worker,
and Independent SAT Witness Verifier for Tier-2 D78 NA-DAG Branches.

Mirrors d9c7_compact_cnf.py's winning 1-pass fixed-core structure (which closed 4/4 D9-C7
cores in 4.7-17.4 min with 0 cuts) generalized to all 22 nonempty Tier-2 D78 branches
(T* in {24, 25, 26, 27}, du <= dv in {7, 8, 9}, c = du + dv - (38 - T*) >= 1).

For a fixed triangle-free core T of order n_T = T* with alpha(T) <= 7:
  - Roots 0 (deg du), 1 (deg dv) are nonadjacent with codegree c = |S|.
  - S = N(0) & N(1) (|S| = c), X = N(0)\\S (|X| = du - c), Y = N(1)\\S (|Y| = dv - c).
  - R = c + nx + ny = 38 - n_T outer rows (11..14).
  - Primary Boolean variables:
      M[r][t]    (R * n_T vars, 297..336) for edges between outer rows S+X+Y and core T,
      E_XY[i][j] (nx * ny vars, 4..36)    for bipartite edges between X and Y.
  - Total primary variables: only 301..378!

All encoded constraints are proved necessary conditions (zero heuristic pruning):
  0. Exact Core-Level Pure-Integer Prefilter:
     Rejects core T immediately if any non-edge (a, b) in T already satisfies
     codeg_T(a, b) > max_cap (violating the branch's tie-broken global codegree cap),
     or if t_lo > t_hi, emitting a directly verifiable pure-integer witness.
  1. Triangle-free with T: M[r][a] & M[r][b] forbidden for all (a,b) in E(T).
  2. Triangle-free across X-Y-T: E_XY[i][j] & M[x_i][t] & M[y_j][t] forbidden.
     When t_min == nx * ny (forced K_{nx, ny}), adds explicit U_X & U_Y = empty and
     exact S-domination deg_S(t) >= max(1, (7 - deg_T(t)) - max(nx, ny)).
  3. Exact D78 degree bounds in {7, 8, 9} for all vertices in S, X, Y, T, plus
     saturation deg_Y(x_i) >= 1, deg_X(y_j) >= 1, and optional pruner t_range [t_lo, t_hi].
  4. Exact A- and B-domination: deg_A(t) >= 1 and deg_B(t) >= 1 for all t in T.
  5. Exact saturation for S -> T (pure clauses) and X/Y -> T (via X-Y-T common neighbors).
  6. Global tie-broken non-edge codegree caps from cap_matrix_tiebroken(T*, du, dv):
     intra-S (<= max_cap - 2), intra-X/Y (<= max_cap - 1), root-to-T/X/Y caps, and
     ONLY nontrivial nonadjacent T-pairs where min(9-deg_T(a), 9-deg_T(b)) > max_cap - codeg_T(a,b).
  7. Exact Hall b=1 private-neighbor bounds on A and B.
  8. Exact static I7(T) hitting-set constraints: for every W in I7(T), at most 2 rows of A
     and at most 2 rows of B may miss W.
  9. Sound lex symmetry breaking: strict lex_lt on S rows, non-strict lex_le on X rows
     and on Y rows, plus M[x_0] <=_lex M[y_0] when du == dv.
"""
import argparse
import gzip
import hashlib
import json
try:
    import resource
except ImportError:
    resource = None
import shutil
import subprocess
import time
from functools import lru_cache
from pathlib import Path

from d78_nadag_pruner import E8, E8MAX, cap_matrix_tiebroken

N_G = 40


def decode_g6(raw: str, expected_n=None):
    """Decode an ASCII graph6 string into a bitmask adjacency list."""
    s = raw.strip().removeprefix('>>graph6<<')
    if not s:
        raise ValueError('Empty graph6 string')
    n = ord(s[0]) - 63
    if expected_n is not None and n != expected_n:
        raise ValueError(f'Expected {expected_n} vertices, got {n}')
    expected_len = 1 + (n * (n - 1) // 2 + 5) // 6
    if len(s) != expected_len:
        raise ValueError(f'Bad graph6 length {len(s)} != {expected_len} for n={n}')
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
    """Encode a bitmask adjacency list (n <= 62) into canonical graph6 ASCII."""
    n = len(adj)
    assert 1 <= n <= 62
    bits = []
    for j in range(n):
        for i in range(j):
            bits.append((adj[i] >> j) & 1)
    while len(bits) % 6:
        bits.append(0)
    chars = [chr(n + 63)]
    for idx in range(0, len(bits), 6):
        val = 0
        for b in bits[idx:idx + 6]:
            val = (val << 1) | b
        chars.append(chr(val + 63))
    return ''.join(chars)


def enum_indep(adj, k: int, limit=None):
    """Enumerate independent k-sets in bitmask graph adj (exact backtracking)."""
    n = len(adj)
    res = []

    def dfs(cand: int, rem: int, cur: int):
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


@lru_cache(maxsize=64)
def _cached_enum_i7(adj_tuple: tuple, limit: int | None):
    return tuple(enum_indep(list(adj_tuple), 7, limit=limit))


def verify_r38_core(adj, expected_n=None, check_alpha=True):
    """Verify adj is a valid triangle-free (3,8; n_T) core with alpha(T) <= 7."""
    n = len(adj)
    if expected_n is not None:
        assert n == expected_n, f'Expected n={expected_n}, got {n}'
    edges = sum(x.bit_count() for x in adj) // 2
    for i in range(n):
        assert not ((adj[i] >> i) & 1), f'Self-loop on {i}'
        d = adj[i].bit_count()
        assert d <= 7, f'Core vertex {i} has deg {d} > 7'
        if n in E8:
            assert d >= n - 23, f'Core vertex {i} has deg {d} < {n - 23}'
        for j in range(i + 1, n):
            assert ((adj[i] >> j) & 1) == ((adj[j] >> i) & 1), f'Asymmetric edge ({i},{j})'
            if (adj[i] >> j) & 1:
                assert (adj[i] & adj[j]) == 0, f'Triangle on ({i},{j})'
    if n in E8:
        assert E8[n] <= edges <= E8MAX[n], f'e(T)={edges} outside [{E8[n]}, {E8MAX[n]}]'
    if check_alpha:
        assert len(enum_indep(adj, 8, limit=1)) == 0, 'Core has an independent 8-set'
    return edges


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
        """Sinz sequential counter enforcing sum(xs) <= k."""
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
        if m == 1:
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
        """Enforce sum(xs) >= k."""
        if k <= 0:
            return
        if k == 1:
            self.add(list(xs))
            return
        if k > len(xs):
            self.add([])
            return
        self.atmost_seq([-x for x in xs], len(xs) - k)

    def exact_seq(self, xs, k: int):
        self.range_seq(xs, k, k)

    def range_seq(self, xs, lo: int, hi: int):
        m = len(xs)
        lo = max(0, lo)
        hi = min(m, hi)
        if lo > hi:
            self.add([])
            return
        if lo == 0 and hi == m:
            return
        if lo == 0:
            self.atmost_seq(xs, hi)
            return
        if hi == m:
            self.atleast_seq(xs, lo)
            return
        if hi == 0:
            for x in xs:
                self.add([-x])
            return
        if lo == m:
            for x in xs:
                self.add([x])
            return
        if m - lo < hi:
            self.range_seq([-x for x in xs], m - hi, m - lo)
            return
        s = [[self.var() for _ in range(hi)] for _ in range(m)]
        self.add([-xs[0], s[0][0]])
        self.add([xs[0], -s[0][0]])
        for j in range(1, hi):
            self.add([-s[0][j]])
        for i in range(1, m):
            self.add([-xs[i], s[i][0]])
            self.add([-s[i - 1][0], s[i][0]])
            self.add([-s[i][0], s[i - 1][0], xs[i]])
            for j in range(1, hi):
                self.add([-xs[i], -s[i - 1][j - 1], s[i][j]])
                self.add([-s[i - 1][j], s[i][j]])
                if j < lo:
                    self.add([-s[i][j], s[i - 1][j], xs[i]])
                    self.add([-s[i][j], s[i - 1][j], s[i - 1][j - 1]])
            self.add([-xs[i], -s[i - 1][hi - 1]])
        self.add([s[m - 1][lo - 1]])

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
        """Enforce bitvector a <= b non-strictly (MSB at index 0)."""
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
            f.write(f'p cnf {self.nv} {total}\n')
            for cl in self.clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')
            for cl in extra_clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')


def build_d78_core_cnf(
    adj_T,
    Tstar: int,
    du: int,
    dv: int,
    t_range=None,
    include_b2: bool = False,
    include_i7: bool = True,
    max_i7: int = 2000,
    include_lex: bool = True,
    d78_strict: bool = True,
    verify_core: bool = True,
):
    """Build compact DIMACS CNF for a Tier-2 D78 branch (T*, du, dv) on fixed core adj_T.

    Returns (cnf, layout, meta). If the fixed core T is already refuted by the branch's
    pure-integer codegree/t-range bounds, returns cnf=None and meta['unsat_by_core_prefilter']=True.
    """
    assert du <= dv and du in (7, 8, 9) and dv in (7, 8, 9)
    assert Tstar in (24, 25, 26, 27)
    shift = 38 - Tstar
    c = du + dv - shift
    nx = du - c
    ny = dv - c
    nT = Tstar
    R = c + nx + ny
    assert R == 38 - nT and c >= 1 and nx >= 0 and ny >= 0

    if verify_core:
        eT = verify_r38_core(adj_T, expected_n=nT, check_alpha=True)
    else:
        assert len(adj_T) == nT
        eT = sum(x.bit_count() for x in adj_T) // 2

    edges_T = [(i, j) for i in range(nT) for j in range(i + 1, nT) if (adj_T[i] >> j) & 1]
    deg_T = [x.bit_count() for x in adj_T]
    cap_tb = cap_matrix_tiebroken(Tstar, du, dv)
    max_cap = cap_tb[3][3]
    cap_u_max = cap_tb[du - 6][3]
    cap_v_max = cap_tb[dv - 6][3]

    S_rows = list(range(0, c))
    X_rows = list(range(c, c + nx))
    Y_rows = list(range(c + nx, R))
    A_rows = S_rows + X_rows
    B_rows = S_rows + Y_rows

    t_lo = max(nx, ny)
    t_hi = nx * ny
    if t_range is not None:
        t_lo = max(t_lo, int(t_range[0]))
        t_hi = min(t_hi, int(t_range[1]))

    unsat_reason = None
    if t_lo > t_hi:
        unsat_reason = {'type': 't_range_empty', 't_lo': t_lo, 't_hi': t_hi}
    if unsat_reason is None:
        for a in range(nT):
            for b in range(a + 1, nT):
                if (adj_T[a] >> b) & 1:
                    continue
                ct = (adj_T[a] & adj_T[b]).bit_count()
                if ct > max_cap:
                    unsat_reason = {
                        'type': 'core_nonedge_codeg_exceeds_max_cap',
                        'a': a, 'b': b, 'codeg_T': ct, 'max_cap': max_cap,
                    }
                    break
            if unsat_reason is not None:
                break

    if unsat_reason is not None:
        meta = {
            'branch_id': f'D78-T{Tstar}-D{du}{dv}-C{c}',
            'Tstar': Tstar, 'du': du, 'dv': dv, 'c': c, 'nx': nx, 'ny': ny, 'eT': eT,
            'unsat_by_core_prefilter': True,
            'unsat_reason': unsat_reason,
            'primary_vars': R * nT + nx * ny,
            'vars': 0,
            'clauses': 0,
        }
        return None, None, meta

    cnf = CompactCNF(1)
    M = [[cnf.var() for _ in range(nT)] for _ in range(R)]
    E_XY = [[cnf.var() for _ in range(ny)] for _ in range(nx)]
    num_primary = cnf.nv
    forced_complete_xy = (t_lo == nx * ny and nx > 0 and ny > 0)

    for r in range(R):
        for a, b in edges_T:
            cnf.add([-M[r][a], -M[r][b]])

    if forced_complete_xy:
        for i in range(nx):
            for j in range(ny):
                cnf.add([E_XY[i][j]])
        ux = [cnf.var() for _ in range(nT)]
        uy = [cnf.var() for _ in range(nT)]
        for t in range(nT):
            for rx in X_rows:
                cnf.add([-M[rx][t], ux[t]])
            cnf.add([-ux[t]] + [M[rx][t] for rx in X_rows])
            for ry in Y_rows:
                cnf.add([-M[ry][t], uy[t]])
            cnf.add([-uy[t]] + [M[ry][t] for ry in Y_rows])
            cnf.add([-ux[t], -uy[t]])
            min_dS = max(1, (7 - deg_T[t]) - max(nx, ny))
            cnf.atleast_seq([M[rs][t] for rs in S_rows], min_dS)
    else:
        for i, rx in enumerate(X_rows):
            for j, ry in enumerate(Y_rows):
                exy = E_XY[i][j]
                for t in range(nT):
                    cnf.add([-exy, -M[rx][t], -M[ry][t]])

    for rs in S_rows:
        cnf.range_seq(M[rs], 5, 7)

    for i, rx in enumerate(X_rows):
        xy_row = E_XY[i]
        cnf.atleast_seq(xy_row, 1)
        cnf.atmost_seq(xy_row, min(ny, cap_v_max))
        cnf.range_seq(M[rx] + xy_row, 6, 8)

    for j, ry in enumerate(Y_rows):
        xy_col = [E_XY[i][j] for i in range(nx)]
        cnf.atleast_seq(xy_col, 1)
        cnf.atmost_seq(xy_col, min(nx, cap_u_max))
        cnf.range_seq(M[ry] + xy_col, 6, 8)

    if not forced_complete_xy and nx > 0 and ny > 0:
        all_xy = [E_XY[i][j] for i in range(nx) for j in range(ny)]
        cnf.range_seq(all_xy, t_lo, t_hi)

    for t in range(nT):
        col = [M[r][t] for r in range(R)]
        lo_col = max(1, 7 - deg_T[t])
        hi_col = 9 - deg_T[t]
        cnf.range_seq(col, lo_col, hi_col)
        cnf.range_seq([M[r][t] for r in A_rows], 1, min(du, cap_u_max, hi_col))
        cnf.range_seq([M[r][t] for r in B_rows], 1, min(dv, cap_v_max, hi_col))

    if d78_strict and du == 9 and dv == 9:
        max_outer_edges = 179 - du - dv - eT
        all_outer = [M[r][t] for r in range(R) for t in range(nT)] + [
            E_XY[i][j] for i in range(nx) for j in range(ny)
        ]
        cnf.atmost_seq(all_outer, max_outer_edges)

    for t in range(nT):
        nbrs = [w for w in range(nT) if (adj_T[t] >> w) & 1]
        for rs in S_rows:
            cnf.add([M[rs][t]] + [M[rs][w] for w in nbrs])

    if forced_complete_xy:
        for t in range(nT):
            nbrs = [w for w in range(nT) if (adj_T[t] >> w) & 1]
            for rx in X_rows:
                cnf.add([M[rx][t], uy[t]] + [M[rx][w] for w in nbrs])
            for ry in Y_rows:
                cnf.add([M[ry][t], ux[t]] + [M[ry][w] for w in nbrs])
    else:
        for i, rx in enumerate(X_rows):
            for t in range(nT):
                nbrs = [w for w in range(nT) if (adj_T[t] >> w) & 1]
                ps = []
                for j, ry in enumerate(Y_rows):
                    p = cnf.var()
                    cnf.add([-p, E_XY[i][j]])
                    cnf.add([-p, M[ry][t]])
                    ps.append(p)
                cnf.add([M[rx][t]] + [M[rx][w] for w in nbrs] + ps)
        for j, ry in enumerate(Y_rows):
            for t in range(nT):
                nbrs = [w for w in range(nT) if (adj_T[t] >> w) & 1]
                ps = []
                for i, rx in enumerate(X_rows):
                    p = cnf.var()
                    cnf.add([-p, E_XY[i][j]])
                    cnf.add([-p, M[rx][t]])
                    ps.append(p)
                cnf.add([M[ry][t]] + [M[ry][w] for w in nbrs] + ps)

    def add_pair_cap(vec1, vec2, cap_val: int):
        bs = []
        for a, b in zip(vec1, vec2):
            v = cnf.var()
            cnf.add([-a, -b, v])
            bs.append(v)
        cnf.atmost_seq(bs, cap_val)

    for i in range(c):
        for j in range(i + 1, c):
            add_pair_cap(M[S_rows[i]], M[S_rows[j]], max_cap - 2)

    for i in range(nx):
        for j in range(i + 1, nx):
            add_pair_cap(M[X_rows[i]] + E_XY[i], M[X_rows[j]] + E_XY[j], max_cap - 1)

    for i in range(ny):
        for j in range(i + 1, ny):
            col_i = [E_XY[k][i] for k in range(nx)]
            col_j = [E_XY[k][j] for k in range(nx)]
            add_pair_cap(M[Y_rows[i]] + col_i, M[Y_rows[j]] + col_j, max_cap - 1)

    nontrivial_t_pairs = 0
    zero_codeg_t_pairs = 0
    for a in range(nT):
        rem_a = 9 - deg_T[a]
        for b in range(a + 1, nT):
            if (adj_T[a] >> b) & 1:
                continue
            ct = (adj_T[a] & adj_T[b]).bit_count()
            cap_ab = max_cap - ct
            need_cap = min(rem_a, 9 - deg_T[b]) > cap_ab
            need_sat = (ct == 0)
            if need_cap or need_sat:
                if need_cap:
                    nontrivial_t_pairs += 1
                if need_sat:
                    zero_codeg_t_pairs += 1
                bs = []
                for r in range(R):
                    v = cnf.var()
                    cnf.add([-M[r][a], -M[r][b], v])
                    if need_sat:
                        cnf.add([-v, M[r][a]])
                        cnf.add([-v, M[r][b]])
                    bs.append(v)
                if need_cap:
                    cnf.atmost_seq(bs, cap_ab)
                if need_sat:
                    cnf.add(bs)

    for r in A_rows:
        otherA = [q for q in A_rows if q != r]
        privA = []
        for t in range(nT):
            pa = cnf.var()
            cnf.add([-M[r][t], pa] + [M[q][t] for q in otherA])
            privA.append(pa)
        cap_priv_A = (10 - du) - (1 if (c == 1 and r in S_rows) else 0)
        cnf.atmost_seq(privA, cap_priv_A)

    for r in B_rows:
        otherB = [q for q in B_rows if q != r]
        privB = []
        for t in range(nT):
            pb = cnf.var()
            cnf.add([-M[r][t], pb] + [M[q][t] for q in otherB])
            privB.append(pb)
        cap_priv_B = (10 - dv) - (1 if (c == 1 and r in S_rows) else 0)
        cnf.atmost_seq(privB, cap_priv_B)

    if include_b2:
        for grp, d_root in ((A_rows, du), (B_rows, dv)):
            if d_root < 9:
                continue
            for i1 in range(len(grp)):
                for i2 in range(i1 + 1, len(grp)):
                    r1, r2 = grp[i1], grp[i2]
                    omit = [r for r in grp if r != r1 and r != r2]
                    hs = []
                    for t in range(nT):
                        h = cnf.var()
                        cnf.add([h] + [M[r][t] for r in omit])
                        hs.append(h)
                    cnf.atmost_seq(hs, 3)

    i7_count = 0
    if include_i7:
        I7 = _cached_enum_i7(tuple(adj_T), max_i7)
        i7_count = len(I7)
        for w in I7:
            vs = [t for t in range(nT) if (w >> t) & 1]
            ms = []
            for r in range(R):
                z = cnf.var()
                cnf.add([z] + [M[r][t] for t in vs])
                ms.append(z)
            # At most 1 of X misses W_7 (W_7 U R_X U {v} is independent): direct binary clauses (0 counter vars)
            for i1 in range(nx):
                for i2 in range(i1 + 1, nx):
                    cnf.add([-ms[X_rows[i1]], -ms[X_rows[i2]]])
            # At most 1 of Y misses W_7 (W_7 U R_Y U {u} is independent): direct binary clauses (0 counter vars)
            for j1 in range(ny):
                for j2 in range(j1 + 1, ny):
                    cnf.add([-ms[Y_rows[j1]], -ms[Y_rows[j2]]])
            # Combined A & B hitting bound: |M(W_7) & S| + 1[any X or Y misses W_7] <= 2
            if c >= 2:
                m_xy = cnf.var()
                for r in X_rows + Y_rows:
                    cnf.add([-ms[r], m_xy])
                if c == 2:
                    cnf.add([-ms[S_rows[0]], -ms[S_rows[1]], -m_xy])
                else:
                    cnf.atmost_seq([ms[rs] for rs in S_rows] + [m_xy], 2)
            # Cross-part independent triple {s, x, y} cut when X-Y is not forced complete
            if not forced_complete_xy and nx > 0 and ny > 0:
                if c == 1:
                    m_s = ms[S_rows[0]]
                else:
                    m_s = cnf.var()
                    for rs in S_rows:
                        cnf.add([-ms[rs], m_s])
                for ix in range(nx):
                    for iy in range(ny):
                        cnf.add([E_XY[ix][iy], -m_s, -ms[X_rows[ix]], -ms[Y_rows[iy]]])

    if include_lex:
        for i in range(c - 1):
            cnf.lex_lt(M[S_rows[i]], M[S_rows[i + 1]])
        for i in range(nx - 1):
            cnf.lex_le(M[X_rows[i]], M[X_rows[i + 1]])
        for i in range(ny - 1):
            cnf.lex_le(M[Y_rows[i]], M[Y_rows[i + 1]])
        if du == dv and nx > 0 and ny > 0:
            cnf.lex_le(M[X_rows[0]], M[Y_rows[0]])

    layout = {
        'Tstar': Tstar, 'du': du, 'dv': dv, 'c': c, 'nx': nx, 'ny': ny, 'nT': nT, 'R': R,
        'S_rows': S_rows, 'X_rows': X_rows, 'Y_rows': Y_rows,
        'M': M, 'E_XY': E_XY, 'num_primary': num_primary,
    }
    meta = {
        'branch_id': f'D78-T{Tstar}-D{du}{dv}-C{c}',
        'Tstar': Tstar, 'du': du, 'dv': dv, 'c': c, 'nx': nx, 'ny': ny, 'eT': eT,
        'unsat_by_core_prefilter': False,
        'primary_vars': num_primary,
        'vars': cnf.nv,
        'clauses': len(cnf.clauses),
        'forced_complete_xy': forced_complete_xy,
        'nontrivial_t_pairs': nontrivial_t_pairs,
        'i7_count': i7_count,
        'include_b2': include_b2,
        'include_i7': include_i7,
        'include_lex': include_lex,
        'd78_strict': d78_strict,
    }
    return cnf, layout, meta


def build_40_graph_d78(adj_T, layout, rows_M, rows_XY):
    """Reconstruct the 40-vertex bitmask graph from (adj_T, rows_M, rows_XY)."""
    c = layout['c']
    nx = layout['nx']
    ny = layout['ny']
    nT = layout['nT']
    R = layout['R']
    g = [0] * N_G

    def add_e(u, v):
        g[u] |= 1 << v
        g[v] |= 1 << u

    t_off = 2 + R
    assert t_off + nT == N_G

    for s in range(c):
        add_e(0, 2 + s)
        add_e(1, 2 + s)
    for i in range(nx):
        add_e(0, 2 + c + i)
    for j in range(ny):
        add_e(1, 2 + c + nx + j)
    for i in range(nx):
        for j in range(ny):
            if (rows_XY[i] >> j) & 1:
                add_e(2 + c + i, 2 + c + nx + j)
    for a in range(nT):
        for b in range(a + 1, nT):
            if (adj_T[a] >> b) & 1:
                add_e(t_off + a, t_off + b)
    for r in range(R):
        u = 2 + r
        m = rows_M[r]
        for t in range(nT):
            if (m >> t) & 1:
                add_e(u, t_off + t)
    return g


def verify_ramsey_3_10_40_witness(adj40) -> dict:
    """Independent zero-dependency verifier for a purported (3,10;40) Ramsey witness."""
    if len(adj40) != N_G:
        return {'valid': False, 'reason': f'Expected 40 vertices, got {len(adj40)}'}
    for i in range(N_G):
        if (adj40[i] >> i) & 1:
            return {'valid': False, 'reason': f'Self-loop at vertex {i}'}
        for j in range(i + 1, N_G):
            if ((adj40[i] >> j) & 1) != ((adj40[j] >> i) & 1):
                return {'valid': False, 'reason': f'Asymmetric adjacency at ({i},{j})'}
            if ((adj40[i] >> j) & 1) and (adj40[i] & adj40[j]):
                w = (adj40[i] & adj40[j]).bit_length() - 1
                return {'valid': False, 'reason': f'Triangle ({i},{j},{w})'}
    i10 = enum_indep(adj40, 10, limit=1)
    if i10:
        verts = [v for v in range(N_G) if (i10[0] >> v) & 1]
        return {'valid': False, 'reason': f'Independent 10-set found: {verts}'}
    degs = [x.bit_count() for x in adj40]
    deg_hist = {}
    for d in degs:
        deg_hist[str(d)] = deg_hist.get(str(d), 0) + 1
    return {
        'valid': True,
        'vertices': N_G,
        'edges': sum(degs) // 2,
        'min_degree': min(degs),
        'max_degree': max(degs),
        'degree_histogram': deg_hist,
    }


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def proof_first_solve_core(
    g6: str,
    Tstar: int,
    du: int,
    dv: int,
    out_dir: Path,
    seconds: int = 1800,
    t_range=None,
    include_b2: bool = False,
    include_i7: bool = True,
    max_i7: int = 2000,
    d78_strict: bool = True,
):
    """Proof-first single-pass Kissat + drat-trim (-L LRAT) + lrat-check loop for one core."""
    out_dir.mkdir(parents=True, exist_ok=True)
    t0 = time.monotonic()
    adj_T = decode_g6(g6, expected_n=Tstar)
    cnf, layout, meta = build_d78_core_cnf(
        adj_T, Tstar, du, dv,
        t_range=t_range,
        include_b2=include_b2,
        include_i7=include_i7,
        max_i7=max_i7,
        include_lex=True,
        d78_strict=d78_strict,
    )
    if meta.get('unsat_by_core_prefilter'):
        report = {
            'g6': g6, 'meta': meta, 'status': 'CERTIFIED_UNSAT',
            'proof_format': 'pure_integer_core_prefilter',
            'iters': 0, 'cuts': 0,
            'total_seconds': round(time.monotonic() - t0, 3),
        }
        (out_dir / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report), flush=True)
        return report

    M = layout['M']
    E_XY = layout['E_XY']
    R = layout['R']
    c = layout['c']
    nx = layout['nx']
    ny = layout['ny']
    nT = layout['nT']
    num_primary = layout['num_primary']
    t_off = 2 + R

    extra_cuts = []
    seen_cuts = set()
    iters = 0
    report = {'g6': g6, 'meta': meta, 'status': 'OPEN', 'iters': 0, 'cuts': 0}

    while time.monotonic() - t0 < seconds:
        iters += 1
        rem_sec = max(5, int(seconds - (time.monotonic() - t0)))
        cnf_path = out_dir / 'leaf.cnf'
        drat_path = out_dir / 'leaf.drat'
        lrat_path = out_dir / 'leaf.lrat'
        cnf.write_dimacs(cnf_path, extra_cuts)

        def cap_fsize():
            if resource is not None:
                resource.setrlimit(resource.RLIMIT_FSIZE, (1024 * 1024 ** 2, 1024 * 1024 ** 2))

        t_solve0 = time.monotonic()
        with open(out_dir / 'kissat.log', 'w') as log:
            r = subprocess.run(
                ['kissat', f'--time={rem_sec}', str(cnf_path), str(drat_path)],
                stdout=log, stderr=subprocess.STDOUT, timeout=rem_sec + 30,
                preexec_fn=cap_fsize if resource is not None else None,
            )
        solve_sec = time.monotonic() - t_solve0

        if r.returncode == 20:
            cnf_sha = sha256_file(cnf_path)
            drat_sha = sha256_file(drat_path)
            t_ver0 = time.monotonic()
            has_lrat_check = bool(shutil.which('lrat-check'))
            drat_cmd = ['drat-trim', str(cnf_path), str(drat_path)]
            if has_lrat_check:
                drat_cmd += ['-L', str(lrat_path)]
            with open(out_dir / 'drat-trim.log', 'w') as log:
                v = subprocess.run(
                    drat_cmd,
                    stdout=log, stderr=subprocess.STDOUT, timeout=max(60, rem_sec),
                )
            ok_drat = (
                v.returncode == 0
                and 's VERIFIED' in (out_dir / 'drat-trim.log').read_text(errors='replace')
            )
            ok_lrat = False
            lrat_sha = None
            if ok_drat and has_lrat_check and lrat_path.exists():
                with open(out_dir / 'lrat-check.log', 'w') as log:
                    lv = subprocess.run(
                        ['lrat-check', str(cnf_path), str(lrat_path)],
                        stdout=log, stderr=subprocess.STDOUT, timeout=max(60, rem_sec),
                    )
                ok_lrat = (
                    lv.returncode == 0
                    and 's VERIFIED' in (out_dir / 'lrat-check.log').read_text(errors='replace')
                )
                if ok_lrat:
                    lrat_sha = sha256_file(lrat_path)
                    with open(lrat_path, 'rb') as fi, gzip.open(out_dir / 'leaf.lrat.gz', 'wb', compresslevel=1) as fo:
                        shutil.copyfileobj(fi, fo)
            ver_sec = time.monotonic() - t_ver0
            if ok_drat:
                with open(drat_path, 'rb') as fi, gzip.open(out_dir / 'leaf.drat.gz', 'wb', compresslevel=1) as fo:
                    shutil.copyfileobj(fi, fo)
                report.update(
                    status='CERTIFIED_UNSAT',
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
                report.update(status='UNSAT_VERIFICATION_FAILED', iters=iters, cuts=len(extra_cuts))
            drat_path.unlink(missing_ok=True)
            lrat_path.unlink(missing_ok=True)
            cnf_path.unlink(missing_ok=True)
            break

        elif r.returncode == 10:
            drat_path.unlink(missing_ok=True)
            vals = set()
            for line in (out_dir / 'kissat.log').read_text(errors='replace').splitlines():
                if line.startswith('v '):
                    for tok in line.split()[1:]:
                        lit = int(tok)
                        if 0 < lit <= num_primary:
                            vals.add(lit)
            rows_M = [sum((1 << t) for t in range(nT) if M[r_idx][t] in vals) for r_idx in range(R)]
            rows_XY = [sum((1 << j) for j in range(ny) if E_XY[i][j] in vals) for i in range(nx)]
            g40 = build_40_graph_d78(adj_T, layout, rows_M, rows_XY)
            i10s = enum_indep(g40, 10, limit=128)
            if not i10s:
                wcheck = verify_ramsey_3_10_40_witness(g40)
                (out_dir / 'witness.txt').write_text(
                    ''.join(''.join(str((g40[i] >> j) & 1) for j in range(N_G)) + '\n' for i in range(N_G))
                )
                (out_dir / 'witness_verified.json').write_text(json.dumps(wcheck, indent=2) + '\n')
                status = 'VERIFIED_WITNESS_R310_40' if wcheck['valid'] else 'WITNESS_CHECK_FAILED'
                report.update(status=status, witness_check=wcheck, iters=iters, cuts=len(extra_cuts))
                break
            added = 0
            for mask in i10s:
                rs = [v - 2 for v in range(2, t_off) if (mask >> v) & 1]
                ts = [v - t_off for v in range(t_off, N_G) if (mask >> v) & 1]
                xs = [r_idx - c for r_idx in rs if c <= r_idx < c + nx]
                ys = [r_idx - (c + nx) for r_idx in rs if c + nx <= r_idx < R]
                cl = [M[r_idx][t] for r_idx in rs for t in ts] + [E_XY[i][j] for i in xs for j in ys]
                assert cl, 'Empty I10 cut!'
                key = tuple(sorted(cl))
                if key not in seen_cuts:
                    seen_cuts.add(key)
                    extra_cuts.append(list(key))
                    added += 1
            assert added > 0
            report.update(iters=iters, cuts=len(extra_cuts))

        else:
            drat_path.unlink(missing_ok=True)
            cnf_path.unlink(missing_ok=True)
            report.update(status='OPEN_TIMEOUT', kissat_exit=r.returncode, iters=iters, cuts=len(extra_cuts))
            break

    report['total_seconds'] = round(time.monotonic() - t0, 3)
    (out_dir / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)
    return report


def main():
    ap = argparse.ArgumentParser(description='Tier-2 D78 Fixed-Core Compact CNF Solver')
    ap.add_argument('--g6', required=True, help='Fixed (3,8; n_T) core in graph6 format')
    ap.add_argument('--tstar', type=int, required=True, choices=[24, 25, 26, 27])
    ap.add_argument('--du', type=int, required=True, choices=[7, 8, 9])
    ap.add_argument('--dv', type=int, required=True, choices=[7, 8, 9])
    ap.add_argument('--t-lo', type=int, default=None)
    ap.add_argument('--t-hi', type=int, default=None)
    ap.add_argument('--out', type=Path, default=Path('out_d78_core'))
    ap.add_argument('--seconds', type=int, default=1800)
    ap.add_argument('--include-b2', action='store_true')
    ap.add_argument('--no-i7', action='store_true')
    ap.add_argument('--max-i7', type=int, default=2000)
    args = ap.parse_args()

    t_range = (args.t_lo, args.t_hi) if (args.t_lo is not None and args.t_hi is not None) else None
    proof_first_solve_core(
        args.g6, args.tstar, args.du, args.dv, args.out,
        seconds=args.seconds, t_range=t_range,
        include_b2=args.include_b2, include_i7=not args.no_i7, max_i7=args.max_i7,
    )


if __name__ == '__main__':
    main()
