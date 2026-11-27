#!/usr/bin/env python3
"""Exact variable & clause bloat audit of v5/v7 SAT encoding on D6-N9-B3-P000-T01, D6-N9-B3-P002-T01, D8-N8-B0-P000-T01."""
import itertools, json
from collections import Counter
from pathlib import Path

N = 40
pairs = list(itertools.combinations(range(N), 2))
edge = {p: i + 1 for i, p in enumerate(pairs)}
def e(i, j): return edge[(i, j) if i < j else (j, i)]

E = {6: 118, 7: 104, 8: 95, 9: 86}
ET = {23: 35, 24: 40, 25: 46, 26: 52, 27: 61, 28: 68}
V = (6, 7, 8, 9)
R = {1: 1, 2: 3, 3: 6, 4: 9, 5: 14, 6: 18, 7: 23, 8: 28, 9: 36}
TRUE = 781

class AuditEnc:
    def __init__(self):
        self.nv = 781; self.nclauses = 1; self.fixed = {781: True}
        self.block_vars = Counter(); self.block_clauses = Counter(); self.cur_block = 'init'
    def set_block(self, name): self.cur_block = name
    def val(self, l):
        v = self.fixed.get(abs(l)); return None if v is None else v == (l > 0)
    def fix(self, l):
        v = self.val(l)
        if v is False: raise ValueError('contradictory fixed graph')
        if v is None:
            self.fixed[abs(l)] = l > 0; self.nclauses += 1; self.block_clauses[self.cur_block] += 1
    def var(self):
        self.nv += 1; self.block_vars[self.cur_block] += 1; return self.nv
    def add(self, ls):
        c = set()
        for l in ls:
            v = self.val(l)
            if v is True or -l in c: return
            if v is None: c.add(l)
        self.nclauses += 1; self.block_clauses[self.cur_block] += 1
    def AND(self, ls):
        xs = []
        for l in ls:
            v = self.val(l)
            if v is False: return -781
            if v is None: xs.append(l)
        if not xs: return 781
        if len(xs) == 1: return xs[0]
        z = self.var()
        for l in xs: self.add([-z, l])
        self.add([z] + [-l for l in xs])
        return z
    def am_seqcounter(self, xs, k):
        n = len(xs)
        if k < 0: self.add([]); return
        if k >= n: return
        if k == 0:
            for l in xs: self.add([-l])
            return
        nvars = (n - 1) * k
        ncls = 1 + (k - 1) + (n - 2) * (2 + 2 * (k - 1) + 1) + 1
        self.nv += nvars; self.block_vars[self.cur_block] += nvars
        self.nclauses += ncls; self.block_clauses[self.cur_block] += ncls
    def am(self, ls, k):
        xs = []
        for l in ls:
            v = self.val(l)
            if v is True: k -= 1
            elif v is None: xs.append(l)
        self.am_seqcounter(xs, k)
    def al(self, ls, k): self.am([-l for l in ls], len(ls) - k)
    def bounds(self, ls, lo, hi): self.am(ls, hi); self.al(ls, lo)
    def addbits(self, x, y):
        out = []; carry = None
        for i in range(max(len(x), len(y))):
            ins = [a[i] for a in (x, y) if i < len(a)]
            if carry is not None: ins.append(carry)
            if len(ins) == 1: out.append(ins[0]); carry = None; continue
            z = self.var(); c = self.var()
            for b in itertools.product((0, 1), repeat=len(ins)):
                premise = [-v if v1 else v for v, v1 in zip(ins, b)]; s = sum(b)
                self.add(premise + [z if s % 2 else -z]); self.add(premise + [c if s >= 2 else -c])
            out.append(z); carry = c
        if carry is not None: out.append(carry)
        return out
    def sum_bits(self, xs):
        level = [[x] for x in xs]
        while len(level) > 1:
            level = [self.addbits(level[i], level[i + 1]) if i + 1 < len(level) else level[i] for i in range(0, len(level), 2)]
        return level[0] if level else []
    def bound_bits(self, b, lo, hi):
        for k in reversed(range(len(b))):
            up = [-b[j] if (hi >> j) & 1 else b[j] for j in range(k + 1, len(b))]
            dn = [-b[j] if (lo >> j) & 1 else b[j] for j in range(k + 1, len(b))]
            if not (hi >> k) & 1: self.add(up + [-b[k]])
            if (lo >> k) & 1: self.add(dn + [b[k]])
    def brange(self, xs, lo, hi):
        known = sum(self.val(x) is True for x in xs); rem = [x for x in xs if self.val(x) is None]
        lo2, hi2 = lo - known, hi - known
        if lo2 > len(rem) or hi2 < 0 or lo2 > hi2: self.add([]); return
        self.bound_bits(self.sum_bits(rem), max(0, lo2), min(len(rem), hi2))
    def unary(self, xs, lim, exact=True):
        if lim <= 0: return []
        known = sum(self.val(x) is True for x in xs); x = [x for x in xs if self.val(x) is None]
        if known >= lim: return [TRUE] * lim
        cap = lim - known
        def gt(a, k): return TRUE if k <= 0 else a[k - 1] if k <= len(a) else -TRUE
        def build(a):
            if len(a) <= 1: return a
            A = build(a[:len(a) // 2]); B = build(a[len(a) // 2:])
            C = [self.var() for _ in range(min(cap, len(A) + len(B)))]
            for i in range(len(A) + 1):
                for j in range(len(B) + 1):
                    k = i + j
                    if 0 < k <= len(C): self.add([-gt(A, i), -gt(B, j), gt(C, k)])
                    if exact and k + 1 <= len(C): self.add([gt(A, i + 1), gt(B, j + 1), -gt(C, k + 1)])
            return C
        return [TRUE] * known + build(x)
    def ge(self, a, k): return TRUE if k <= 0 else a[k - 1] if k <= len(a) else -TRUE
    def lex(self, a, b):
        p = 781
        for x, y in zip(a, b):
            self.add([-p, x, -y]); z = self.var()
            self.add([-z, p]); self.add([-z, -x, y]); self.add([-z, x, -y])
            self.add([-p, -x, -y, z]); self.add([-p, x, y, z]); p = z

def groups(d, q):
    X = list(range(2, d + 1)); Y = list(range(d + 1, d + q)); T = list(range(d + q, 40))
    return X, Y, T, [1] + X, [0] + Y

def audit_task(task):
    d, q, m = task['d'], task['q'], task['m']
    ns = [tuple(n) for n in task['profiles']]; s = [(n, m) for n in ns]
    z = AuditEnc(); X, Y, T, A, B = groups(d, q); H0, H1 = Y + T, X + T
    z.set_block('1_skeleton_fixed')
    for i in range(1, N): z.fix(e(0, i) if i in A else -e(0, i))
    for i in range(2, N): z.fix(e(1, i) if i in B else -e(1, i))
    for C in [A, B]:
        for i, j in itertools.combinations(C, 2): z.fix(-e(i, j))
    z.set_block('2_triangles')
    for i, j, k in itertools.combinations(range(N), 3): z.add([-e(i, j), -e(i, k), -e(j, k)])
    z.set_block('3_vertex_degrees')
    deg = {}
    for i in range(N):
        deg[i] = z.unary([e(i, j) for j in range(N) if j != i], 10, True)
        low = d if i == 0 else q if i == 1 else (q if i in X else 6)
        z.add([z.ge(deg[i], low)]); z.add([-z.ge(deg[i], 10)])
    z.set_block('4_profile_histogram')
    count = {k: z.unary([z.AND([z.ge(deg[i], k), -z.ge(deg[i], k + 1)]) for i in range(N)], max(n[k - 6] for n, mm in s) + 1, True) for k in V}
    sels = []
    for n, mm in s:
        h = z.var(); sels.append(h)
        for k, num in zip(V, n): z.add([-h, z.ge(count[k], num)]); z.add([-h, -z.ge(count[k], num + 1)])
    z.add(sels)
    z.set_block('5_edge_counts_m_H0_H1_T_t')
    z.brange(list(edge.values()), m, m)
    z.brange([e(i, j) for i, j in itertools.combinations(H0, 2)], E[d], 180 - 9 * d)
    z.brange([e(i, j) for i, j in itertools.combinations(H1, 2)], E[q], 4 * len(H1))
    z.brange([e(i, j) for i, j in itertools.combinations(T, 2)], ET[len(T)], 4 * len(T))
    z.brange([e(i, j) for i in X for j in Y], task['tlo'], task['thi'])
    z.set_block('6_dual_internal_degrees')
    for H, k in [(H0, d), (H1, q)]:
        for i in H: z.bounds([e(i, j) for j in H if i != j], 11 - k, 8)
    z.set_block('7_codegrees_and_saturation')
    for i, j in pairs:
        if z.val(e(i, j)) is True: continue
        ws = [z.AND([e(i, k), e(j, k)]) for k in range(N) if k not in (i, j)]
        z.add([e(i, j)] + ws); cs = z.unary(ws, 8, False)
        for a in V:
            for b in V: z.add([z.ge(deg[i], a + 1), z.ge(deg[j], b + 1), -z.ge(cs, a + b - 10)])
    z.set_block('8_deficit_eps_sums')
    lim = max(0, max(E[k] + 9 * k - m for k in V))
    if lim:
        for i in range(N):
            ws = [z.AND([e(i, j), -z.ge(deg[j], k + 1)]) for j in range(N) if i != j for k in (6, 7, 8)]
            eps = z.unary(ws, lim, True)
            for k in V:
                l = E[k] + 9 * k - m
                if l > 0: z.add([-z.ge(deg[i], k), z.ge(deg[i], k + 1), z.ge(eps, l)])
    z.set_block('9_HB_neighborhood_patterns')
    for nb, H in [(A, H0), (B, H1)]:
        k = len(nb)
        for b in range(1, min(4, k - 2) + 1):
            for sub in itertools.combinations(nb, b):
                omit = [u for u in nb if u not in sub]
                w = [z.AND([-e(v, u) for u in omit]) for v in H]
                z.am(w, R[10 - k + b] - 1 - b)
                for a in sub: z.am([z.AND([t, e(v, a)]) for t, v in zip(w, H)], 9 - k + b)
    z.set_block('10_lex_symmetry')
    for C in (X, Y, T):
        for i, j in zip(C, C[1:]):
            ks = [k for k in range(N) if k not in (i, j)]
            z.lex([e(i, k) for k in ks], [e(j, k) for k in ks])
    z.set_block('11_static_seeded_I10')
    seen_cuts = set(); cut_lens = Counter()
    def seed_cut(ss):
        c = [e(i, j) for i, j in itertools.combinations(sorted(ss), 2)]
        if any(z.val(x) is True for x in c): return
        proj = tuple(x for x in c if z.val(x) is None)
        if proj not in seen_cuts:
            seen_cuts.add(proj); cut_lens[len(proj)] += 1; z.nclauses += 1; z.block_clauses['11_static_seeded_I10'] += 1
    for ss in itertools.combinations(X + Y, 10): seed_cut(ss)
    for nb, H in ((A, H0), (B, H1)):
        for ss in itertools.combinations(H, 10 - len(nb)): seed_cut(tuple(nb) + ss)
    return {'task_id': task['id'], 'total_vars': z.nv, 'total_clauses_with_seeds': z.nclauses,
            'block_vars': dict(z.block_vars), 'block_clauses': dict(z.block_clauses), 'seed_cut_lengths': dict(sorted(cut_lens.items()))}

if __name__ == '__main__':
    all_tasks = json.loads(Path('all_tasks.json').read_text())
    for tid in ['D6-N9-B3-P000-T01', 'D6-N9-B3-P002-T01', 'D8-N8-B0-P000-T01']:
        print(json.dumps(audit_task(all_tasks[tid]), indent=2))
