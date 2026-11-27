#!/usr/bin/env python3
"""
Lean-CNF + SMS (SAT Modulo Symmetries) Generator for Ramsey R(3,10) V8 (Ultra-Lean v2).
Eliminates ALL 4 major bloat sources from v5/v7 (380k-426k vars -> 9k-28k vars, 15x-42x smaller).
"""
import argparse, itertools, json
from collections import Counter
from pathlib import Path
from reconstruct_tasks import feasible_v8

N = 40; pairs = list(itertools.combinations(range(N), 2))
edge = {p: i + 1 for i, p in enumerate(pairs)}
def e(i, j): return edge[(i, j) if i < j else (j, i)]

V = (6, 7, 8, 9); E = {6: 118, 7: 104, 8: 95, 9: 86}; ET = {23: 35, 24: 40, 25: 46, 26: 52, 27: 61, 28: 68}; TRUE = 781

class LeanCNF:
    def __init__(self):
        self.nv = 781; self.clauses = [[TRUE]]; self.fixed = {TRUE: True}
        self.block_vars = Counter(); self.block_clauses = Counter(); self.cur_block = 'init'
    def set_block(self, name): self.cur_block = name
    def val(self, l):
        v = self.fixed.get(abs(l)); return None if v is None else v == (l > 0)
    def fix(self, l):
        v = self.val(l)
        if v is False: self.clauses.append([]); self.block_clauses[self.cur_block] += 1; return
        if v is None: self.fixed[abs(l)] = l > 0; self.clauses.append([l]); self.block_clauses[self.cur_block] += 1
    def var(self): self.nv += 1; self.block_vars[self.cur_block] += 1; return self.nv
    def add(self, ls):
        c = set()
        for l in ls:
            v = self.val(l)
            if v is True or -l in c: return
            if v is None: c.add(l)
        self.clauses.append(sorted(c, key=lambda x: (abs(x), x))); self.block_clauses[self.cur_block] += 1
    def AND(self, ls):
        xs = []
        for l in ls:
            v = self.val(l)
            if v is False: return -TRUE
            if v is None: xs.append(l)
        if not xs: return TRUE
        if len(xs) == 1: return xs[0]
        z = self.var()
        for l in xs: self.add([-z, l])
        self.add([z] + [-l for l in xs]); return z
    def unary(self, xs, lim, exact=True):
        if lim <= 0: return []
        known = sum(self.val(x) is True for x in xs); x = [x for x in xs if self.val(x) is None]
        if known >= lim: return [TRUE] * lim
        cap = lim - known
        def gt(a, k): return TRUE if k <= 0 else a[k - 1] if k <= len(a) else -TRUE
        def build(a):
            if len(a) <= 1: return a
            mid = len(a) // 2; A = build(a[:mid]); B = build(a[mid:])
            C = [self.var() for _ in range(min(cap, len(A) + len(B)))]
            for i in range(len(A) + 1):
                for j in range(len(B) + 1):
                    k = i + j
                    if 0 < k <= len(C): self.add([-gt(A, i), -gt(B, j), gt(C, k)])
                    if exact and k + 1 <= len(C): self.add([gt(A, i + 1), gt(B, j + 1), -gt(C, k + 1)])
            return C
        return [TRUE] * known + build(x)
    def ge(self, a, k): return TRUE if k <= 0 else a[k - 1] if k <= len(a) else -TRUE
    def cond_lex_ge(self, cond_lit, a, b):
        p = cond_lit
        for x, y in zip(a, b):
            self.add([-p, x, -y]); z = self.var()
            self.add([-z, p]); self.add([-z, -x, y]); self.add([-z, x, -y])
            self.add([-p, -x, -y, z]); self.add([-p, x, y, z]); p = z
    def write_dimacs(self, path):
        with open(path, 'w') as f:
            f.write(f"p cnf {self.nv} {len(self.clauses)}\n")
            for cl in self.clauses: f.write(' '.join(map(str, cl)) + ' 0\n')

def groups(d, q):
    X = list(range(2, d + 1)); Y = list(range(d + 1, d + q)); T = list(range(d + q, 40))
    return X, Y, T, [1] + X, [0] + Y

def build_lean_cnf(task, sym_mode='static_lex', include_xy_codeg=True, include_b1_singletons=True, max_seed_len=16):
    d, q, m = task['d'], task['q'], task['m']; ns = [tuple(n) for n in task['profiles']]
    X, Y, T, A, B = groups(d, q); H0, H1 = Y + T, X + T; nx, ny, nt = len(X), len(Y), len(T)
    konig_lb = max(0, d + q - 11)
    allowed_pairs = [(n, tv) for n in ns for tv in feasible_v8(n, m, d, q)[1] if max(task['tlo'], konig_lb) <= tv <= task['thi']]
    z = LeanCNF()
    if not allowed_pairs:
        z.set_block('0_prefilter_unsat'); z.add([])
        return z, {'unsat_by_prefilter': True, 'allowed_pairs': 0, 'total_vars': z.nv, 'total_clauses': len(z.clauses)}

    surv_ns = sorted({n for n, _ in allowed_pairs}); surv_ts = sorted({tv for _, tv in allowed_pairs})
    possible_degs = sorted({V[k] for n in surv_ns for k in range(4) if n[k] > 0})

    z.set_block('1_skeleton_fixed')
    for i in range(1, N): z.fix(e(0, i) if i in A else -e(0, i))
    for i in range(2, N): z.fix(e(1, i) if i in B else -e(1, i))
    for C in (A, B):
        for i, j in itertools.combinations(C, 2): z.fix(-e(i, j))

    z.set_block('2_triangles')
    for i, j, k in itertools.combinations(range(N), 3): z.add([-e(i, j), -e(i, k), -e(j, k)])

    z.set_block('3_vertex_degrees')
    deg = {}
    for i in range(N):
        deg[i] = z.unary([e(i, j) for j in range(N) if j != i], 10, True)
        lo = d if i == 0 else q if i == 1 else (q if i in X else 6)
        hi = d if i == 0 else q if i == 1 else 9
        z.add([z.ge(deg[i], lo)]); z.add([-z.ge(deg[i], hi + 1)])
        for k in range(lo, hi + 1):
            if k not in possible_degs and i >= 2: z.add([-z.ge(deg[i], k), z.ge(deg[i], k + 1)])

    z.set_block('4_profile_and_t_joint')
    t_u = z.unary([e(x, y) for x in X for y in Y], surv_ts[-1] + 1, True)
    z.add([z.ge(t_u, surv_ts[0])]); z.add([-z.ge(t_u, surv_ts[-1] + 1)])
    count = {k: z.unary([z.AND([z.ge(deg[i], k), -z.ge(deg[i], k + 1)]) for i in range(N)], max(n[k - 6] for n in surv_ns) + 1, True)
             for k in V if k in possible_degs}
    sels = []
    for n in surv_ns:
        ts_for_n = sorted({tv for nn, tv in allowed_pairs if nn == n})
        h = z.var(); sels.append(h)
        for k, num in zip(V, n):
            if k in count: z.add([-h, z.ge(count[k], num)]); z.add([-h, -z.ge(count[k], num + 1)])
        z.add([-h, z.ge(t_u, ts_for_n[0])]); z.add([-h, -z.ge(t_u, ts_for_n[-1] + 1)])
        for tv in range(ts_for_n[0], ts_for_n[-1] + 1):
            if tv not in ts_for_n: z.add([-h, -z.ge(t_u, tv), z.ge(t_u, tv + 1)])
    z.add(sels)

    z.set_block('5_algebraic_edge_bounds')
    h0_max = min(180 - 9 * d, (7 * len(H0) + d * (10 - d)) // 2)
    h1_max = min(4 * len(H1), (7 * len(H1) + q * (10 - q)) // 2)
    defX_lits = [-z.ge(deg[x], k + 1) for x in X for k in (6, 7, 8) if k >= q and any(v <= k for v in possible_degs)]
    defY_lits = [-z.ge(deg[y], k + 1) for y in Y for k in (6, 7, 8) if any(v <= k for v in possible_degs)]
    u_defX = z.unary(defX_lits, len(defX_lits), True) if defX_lits else []
    u_defY = z.unary(defY_lits, len(defY_lits), True) if defY_lits else []
    defX_lo, defX_hi = max(0, E[d] - (m - q - 9 * nx)), min(len(defX_lits), h0_max - (m - q - 9 * nx))
    if defX_lo > defX_hi: z.add([])
    else:
        if defX_lo > 0: z.add([z.ge(u_defX, defX_lo)])
        if defX_hi < len(defX_lits): z.add([-z.ge(u_defX, defX_hi + 1)])
    defY_lo, defY_hi = max(0, E[q] - (m - d - 9 * ny)), min(len(defY_lits), h1_max - (m - d - 9 * ny))
    if defY_lo > defY_hi: z.add([])
    else:
        if defY_lo > 0: z.add([z.ge(u_defY, defY_lo)])
        if defY_hi < len(defY_lits): z.add([-z.ge(u_defY, defY_hi + 1)])
    defXY_lits = defX_lits + defY_lits
    u_defXY = z.unary(defXY_lits, len(defXY_lits), True) if defXY_lits else []
    base_T = m - 1 - 9 * (nx + ny)
    for tv in surv_ts:
        need_lo, need_hi = ET[nt] - base_T - tv, 4 * nt - base_T - tv
        t_eq = [-z.ge(t_u, tv), z.ge(t_u, tv + 1)]
        if need_lo > len(defXY_lits) or need_hi < 0 or need_lo > need_hi: z.add(t_eq)
        else:
            if need_lo > 0: z.add(t_eq + [z.ge(u_defXY, need_lo)])
            if need_hi < len(defXY_lits): z.add(t_eq + [-z.ge(u_defXY, need_hi + 1)])

    z.set_block('6_cross_degrees_and_root_codeg')
    degX, degY = {}, {}
    for v in T:
        degX[v] = z.unary([e(v, x) for x in X], nx, True); degY[v] = z.unary([e(v, y) for y in Y], ny, True)
        z.add([z.ge(degX[v], 1)]); z.add([z.ge(degY[v], 1)])
        for k in possible_degs:
            if k + d - 11 < nx: z.add([z.ge(deg[v], k + 1), -z.ge(degX[v], k + d - 10)])
            if k + q - 11 < ny: z.add([z.ge(deg[v], k + 1), -z.ge(degY[v], k + q - 10)])
    for x in X:
        degY[x] = z.unary([e(x, y) for y in Y], min(ny, q - 2), True)
        for k in possible_degs:
            if k >= q and k + q - 12 < ny: z.add([z.ge(deg[x], k + 1), -z.ge(degY[x], k + q - 11)])
    for y in Y:
        degX[y] = z.unary([e(x, y) for x in X], min(nx, d - 2), True)
        for k in possible_degs:
            if k + d - 12 < nx: z.add([z.ge(deg[y], k + 1), -z.ge(degX[y], k + d - 11)])

    z.set_block('7_selective_xy_codegrees')
    if include_xy_codeg:
        for gp in (itertools.combinations(X, 2), itertools.combinations(Y, 2)):
            for i, j in gp:
                ws = [z.AND([e(i, k), e(j, k)]) for k in range(N) if k not in (i, j) and z.val(e(i, k)) is not False and z.val(e(j, k)) is not False]
                cs = z.unary(ws, 8, False)
                for a in possible_degs:
                    for b in possible_degs:
                        if a + b - 11 < 8: z.add([z.ge(deg[i], a + 1), z.ge(deg[j], b + 1), -z.ge(cs, a + b - 10)])

    z.set_block('8_deficit_eps_sums')
    if max(0, max(E[k] + 9 * k - m for k in possible_degs)):
        for i in range(N):
            lo_i = d if i == 0 else q if i == 1 else (q if i in X else 6)
            hi_i = d if i == 0 else q if i == 1 else 9
            trig = [k for k in possible_degs if lo_i <= k <= hi_i and E[k] + 9 * k - m > 0]
            if not trig: continue
            ws = [z.AND([e(i, j), -z.ge(deg[j], k + 1)]) for j in range(N) if j != i and z.val(e(i, j)) is not False
                  for k in (6, 7, 8) if any(v <= k for v in possible_degs)]
            eps = z.unary(ws, max(E[k] + 9 * k - m for k in trig), False)
            for k in trig: z.add([-z.ge(deg[i], k), z.ge(deg[i], k + 1), z.ge(eps, E[k] + 9 * k - m)])

    z.set_block('9_HB_b1_singletons_only')
    if include_b1_singletons:
        for x in X:
            u = z.unary([z.AND([-z.ge(degX[v], 2), e(v, x)]) for v in T], 10 - d + 1, False); z.add([-z.ge(u, 10 - d + 1)])
        for y in Y:
            u = z.unary([z.AND([-z.ge(degY[v], 2), e(v, y)]) for v in T], 10 - q + 1, False); z.add([-z.ge(u, 10 - q + 1)])

    z.set_block('10_symmetry_breaking')
    sms_partition = [[0], [1], X, Y, T]
    if sym_mode == 'static_lex':
        for i in range(nx - 1):
            u, v = X[i], X[i + 1]
            ku = [z.ge(deg[u], k) for k in (9, 8, 7)] + [z.ge(degY[u], k) for k in range(min(ny, q - 2), 0, -1)]
            kv = [z.ge(deg[v], k) for k in (9, 8, 7)] + [z.ge(degY[v], k) for k in range(min(ny, q - 2), 0, -1)]
            z.cond_lex_ge(TRUE, ku + [e(u, k) for k in Y + T], kv + [e(v, k) for k in Y + T])
        for i in range(ny - 1):
            u, v = Y[i], Y[i + 1]
            ku = [z.ge(deg[u], k) for k in (9, 8, 7)] + [z.ge(degX[u], k) for k in range(min(nx, d - 2), 0, -1)]
            kv = [z.ge(deg[v], k) for k in (9, 8, 7)] + [z.ge(degX[v], k) for k in range(min(nx, d - 2), 0, -1)]
            z.cond_lex_ge(TRUE, ku + [e(u, k) for k in X + T], kv + [e(v, k) for k in X + T])
        for i in range(nt - 1):
            u, v = T[i], T[i + 1]
            ku = [z.ge(deg[u], k) for k in (9, 8, 7)] + [z.ge(degX[u], k) for k in range(nx, 0, -1)] + [z.ge(degY[u], k) for k in range(ny, 0, -1)]
            kv = [z.ge(deg[v], k) for k in (9, 8, 7)] + [z.ge(degX[v], k) for k in range(nx, 0, -1)] + [z.ge(degY[v], k) for k in range(ny, 0, -1)]
            z.cond_lex_ge(TRUE, ku + [e(u, k) for k in X + Y], kv + [e(v, k) for k in X + Y])

    z.set_block('11_short_projected_I10')
    seen_cuts = set(); cut_lens = Counter()
    def try_seed(ss):
        c = [e(i, j) for i, j in itertools.combinations(sorted(ss), 2)]
        if any(z.val(x) is True for x in c): return
        proj = tuple(x for x in c if z.val(x) is None)
        if len(proj) <= max_seed_len and proj not in seen_cuts:
            seen_cuts.add(proj); cut_lens[len(proj)] += 1; z.add(list(proj))
    for ss in itertools.combinations(X + Y, 10): try_seed(ss)
    for nb, H in ((A, H0), (B, H1)):
        if 10 - len(nb) <= 3:
            for ss in itertools.combinations(H, 10 - len(nb)): try_seed(tuple(nb) + ss)

    return z, {'task_id': task['id'], 'sym_mode': sym_mode, 'sms_partition_sizes': [len(g) for g in sms_partition],
               'allowed_profile_t_pairs': len(allowed_pairs), 'total_vars': z.nv, 'total_clauses': len(z.clauses),
               'block_vars': dict(z.block_vars), 'block_clauses': dict(z.block_clauses), 'seed_cut_lengths': dict(sorted(cut_lens.items()))}
