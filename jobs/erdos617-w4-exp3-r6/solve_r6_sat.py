#!/usr/bin/env python3
"""
Exact SAT elimination / verification for Erdős Problem #617 (r=6, K_37),
Profiles #6 (7,7,7,6,5,5), #7 (8,6,6,6,6,5), #8 (7,7,6,6,6,5), #9 (7,6,6,6,6,6).
"""
import argparse
import sys
import time
from math import comb
from itertools import combinations, product
from pysat.solvers import Solver

def emin(n, r=6):
    q, rem = divmod(n, r)
    return rem * comb(q + 1, 2) + (r - rem) * comb(q, 2)

class CNF:
    def __init__(self):
        self.nvars = 0
        self.clauses = []

    def new_var(self):
        self.nvars += 1
        return self.nvars

    def add(self, *lits):
        self.clauses.append(list(lits))

    def add_at_most_k(self, lits, k):
        n = len(lits)
        if k < 0:
            self.add()
            return
        if k >= n:
            return
        if k == 0:
            for l in lits:
                self.add(-l)
            return
        s = [[self.new_var() for _ in range(k)] for _ in range(n - 1)]
        self.add(-lits[0], s[0][0])
        for j in range(1, k):
            self.add(-s[0][j])
        for i in range(1, n - 1):
            self.add(-lits[i], s[i][0])
            self.add(-s[i - 1][0], s[i][0])
            for j in range(1, k):
                self.add(-lits[i], -s[i - 1][j - 1], s[i][j])
                self.add(-s[i - 1][j], s[i][j])
            self.add(-lits[i], -s[i - 1][k - 1])
        self.add(-lits[n - 1], -s[n - 2][k - 1])

    def add_at_least_k(self, lits, k):
        if k <= 0:
            return
        self.add_at_most_k([-l for l in lits], len(lits) - k)

    def add_totalizer(self, lits, max_val=None):
        n = len(lits)
        if max_val is None or max_val > n:
            max_val = n
        if n == 0 or max_val == 0:
            return []
        if n == 1:
            return [lits[0]]
        mid = n // 2
        left = self.add_totalizer(lits[:mid], max_val)
        right = self.add_totalizer(lits[mid:], max_val)
        m = min(len(left) + len(right), max_val)
        out = [self.new_var() for _ in range(m)]
        for a in range(len(left) + 1):
            for b in range(len(right) + 1):
                c = a + b
                if 1 <= c <= m:
                    cl = [out[c - 1]]
                    if a > 0: cl.append(-left[a - 1])
                    if b > 0: cl.append(-right[b - 1])
                    self.add(*cl)
                if c < m:
                    cl = [-out[c]]
                    if a < len(left): cl.append(left[a])
                    if b < len(right): cl.append(right[b])
                    self.add(*cl)
        return out

def build_cnf(parts, r=6, fixed_m=None, trans_parts=None, max_edges_override=None, sym_break=True):
    n = sum(parts)
    assert len(parts) == r
    in_pairs = sum(comb(a, 2) for a in parts)
    e_turan = emin(n, r)
    max_e_g1 = (comb(n, 2) // r) if max_edges_override is None else max_edges_override
    max_t = (comb(n, 2) // r) - e_turan
    min_m = [(r - 1) * emin(a, r) for a in parts]

    part_verts = []
    v_part = []
    cur = 0
    for idx, sz in enumerate(parts):
        part_verts.append(list(range(cur, cur + sz)))
        v_part.extend([idx] * sz)
        cur += sz

    cnf = CNF()
    x = {}
    y = {}
    for u in range(n):
        for v in range(u + 1, n):
            if v_part[u] == v_part[v]:
                x[(u, v)] = cnf.new_var()
            else:
                y[(u, v)] = cnf.new_var()

    # m_i constraints
    m_tot = []
    for i in range(r):
        lits = [x[(u, v)] for u, v in combinations(part_verts[i], 2)]
        if fixed_m is not None:
            tot = cnf.add_totalizer(lits, fixed_m[i] + 1)
            if fixed_m[i] > 0:
                cnf.add(tot[fixed_m[i] - 1])
            if fixed_m[i] < len(tot):
                cnf.add(-tot[fixed_m[i]])
            m_tot.append(None)
        else:
            tot = cnf.add_totalizer(lits, max_t + 1)
            if min_m[i] > 0:
                cnf.add(tot[min_m[i] - 1])
            m_tot.append(tot)

    # Global m_in, m_out constraints via compact totalizers
    all_y = list(y.values())
    if fixed_m is not None:
        m_in_val = sum(fixed_m)
        s_val = [fixed_m[i] - min_m[i] for i in range(r)]
        max_mout = max_e_g1 - in_pairs + m_in_val
        min_mout = max(0, 2 * m_in_val + e_turan - in_pairs) if max_edges_override is None else 0
        if min_mout > max_mout:
            cnf.add()
            return cnf, x, y, v_part, part_verts
        ytot = cnf.add_totalizer(all_y, max_mout + 1)
        if max_mout < len(ytot):
            cnf.add(-ytot[max_mout])
        if min_mout > 0:
            cnf.add(ytot[min_mout - 1])
    else:
        max_mout_global = max_e_g1 - in_pairs + max_t
        m_in_tot = cnf.add_totalizer(list(x.values()), max_t + 1)
        if max_t < len(m_in_tot):
            cnf.add(-m_in_tot[max_t])
        m_out_tot = cnf.add_totalizer(all_y, max_mout_global + 1)
        if max_mout_global < len(m_out_tot):
            cnf.add(-m_out_tot[max_mout_global])
        for k in range(sum(min_m), max_t + 1):
            ub = max_e_g1 - in_pairs + k
            if ub < max_mout_global and k < len(m_in_tot) and ub < len(m_out_tot):
                cnf.add(m_in_tot[k], -m_out_tot[ub])
            if max_edges_override is None:
                lb = 2 * k + e_turan - in_pairs
                if lb > 0 and k - 1 < len(m_in_tot) and lb - 1 < len(m_out_tot):
                    cnf.add(-m_in_tot[k - 1], m_out_tot[lb - 1])

    # Unary totalizers for d_miss[v] and d_cross[v, j]
    dm_tot = {}
    for v in range(n):
        pi = v_part[v]
        if fixed_m is not None and fixed_m[pi] == 0:
            dm_tot[v] = []
        else:
            mlits = [x[(min(v, w), max(v, w))] for w in part_verts[pi] if w != v]
            dm_tot[v] = cnf.add_totalizer(mlits, parts[pi] - 1)

    dc_tot = {}
    for v in range(n):
        pi = v_part[v]
        for j in range(r):
            if j == pi:
                continue
            clits = [y[(min(v, w), max(v, w))] for w in part_verts[j]]
            dc_tot[(v, j)] = cnf.add_totalizer(clits, parts[j])

    # 1. Min-defect local optimality: d_G1(v, A_j) + d_miss(v) <= a_j
    for v in range(n):
        pi = v_part[v]
        if not dm_tot[v]:
            continue
        for j in range(r):
            if j == pi:
                continue
            aj = parts[j]
            for a in range(1, len(dm_tot[v]) + 1):
                rem = aj - a
                if rem < 0:
                    cnf.add(-dm_tot[v][a - 1])
                elif rem < len(dc_tot[(v, j)]):
                    cnf.add(-dm_tot[v][a - 1], -dc_tot[(v, j)][rem])

    # 2. Generalized Property (L) & 3. Sharpened Pairwise Cross-Edge
    for i in range(r):
        if parts[i] < r:
            continue
        ki = parts[i] - r
        if fixed_m is not None:
            si = s_val[i]
            cap = ki + 1 + si
            for v in range(n):
                if v_part[v] != i and cap < len(dc_tot[(v, i)]):
                    cnf.add(-dc_tot[(v, i)][cap])
            if si > 0:
                for j in range(r):
                    if j == i:
                        continue
                    ex_lits = []
                    for v in part_verts[j]:
                        for t in range(ki + 1, min(cap, len(dc_tot[(v, i)]))):
                            ex_lits.append(dc_tot[(v, i)][t])
                    cnf.add_at_most_k(ex_lits, si + fixed_m[j])
        else:
            for v in range(n):
                if v_part[v] == i:
                    continue
                for q in range(0, max_t - min_m[i] + 1):
                    cap = ki + 1 + q
                    if cap < len(dc_tot[(v, i)]) and min_m[i] + q < len(m_tot[i]):
                        cnf.add(m_tot[i][min_m[i] + q], -dc_tot[(v, i)][cap])

    # 4. Pairwise Exact Turan Bound (when fixed_m is given)
    if fixed_m is not None:
        for i in range(r):
            for j in range(i + 1, r):
                NT = parts[i] + parts[j]
                rhs = parts[i] * parts[j] - (r - 1) * emin(NT, r) + fixed_m[i] + fixed_m[j]
                lits = [y[(u, v)] for u in part_verts[i] for v in part_verts[j]]
                if rhs < len(lits):
                    cnf.add_at_most_k(lits, rhs)

    # 5. Symmetry breaking
    if sym_break:
        for i in range(r):
            if fixed_m is not None and fixed_m[i] == 0:
                continue
            vs = part_verts[i]
            for idx in range(len(vs) - 1):
                for k in range(len(dm_tot[vs[idx]])):
                    cnf.add(-dm_tot[vs[idx + 1]][k], dm_tot[vs[idx]][k])
        if fixed_m is None:
            for i in range(r - 1):
                if parts[i] == parts[i + 1]:
                    for k in range(len(m_tot[i])):
                        cnf.add(-m_tot[i + 1][k], m_tot[i][k])

    # 6. Exact Transversal-No-Alpha(r+1) Clauses for i in trans_parts
    if trans_parts is None:
        trans_parts = [0]
    for i in trans_parts:
        if fixed_m is not None and fixed_m[i] == 0:
            continue
        others = [j for j in range(r) if j != i]
        other_lists = [part_verts[j] for j in others]
        pairs_i = list(combinations(part_verts[i], 2))
        for W in product(*other_lists):
            tW = cnf.new_var()
            cl_t = [tW]
            for a_idx in range(r - 1):
                for b_idx in range(a_idx + 1, r - 1):
                    u, v = W[a_idx], W[b_idx]
                    cl_t.append(y[(min(u, v), max(u, v))])
            cnf.add(*cl_t)
            for u, v in pairs_i:
                cl = [-x[(u, v)], -tW]
                for w in W:
                    cl.append(y[(min(u, w), max(u, w))])
                    cl.append(y[(min(v, w), max(v, w))])
                cnf.add(*cl)

    return cnf, x, y, v_part, part_verts

def run_solve(label, parts, r=6, fixed_m=None, trans_parts=None, max_edges_override=None, solver_name="cadical195"):
    t0 = time.time()
    cnf, x, y, v_part, part_verts = build_cnf(
        parts, r=r, fixed_m=fixed_m, trans_parts=trans_parts, max_edges_override=max_edges_override
    )
    t_enc = time.time() - t0
    print(f"[{label}] Encoded: {cnf.nvars} vars, {len(cnf.clauses)} clauses in {t_enc:.2f}s. Solving with {solver_name}...", flush=True)
    t1 = time.time()
    with Solver(name=solver_name, bootstrap_with=cnf.clauses) as s:
        res = s.solve()
        t_sol = time.time() - t1
        if not res:
            print(f"[{label}] *** UNSAT *** ({solver_name}) in {t_sol:.2f}s!", flush=True)
            return "UNSAT"
        else:
            model = set(l for l in s.get_model() if l > 0)
            m_vals = [sum(1 for u, v in combinations(part_verts[i], 2) if x[(u, v)] in model) for i in range(r)]
            mout = sum(1 for var in y.values() if var in model)
            E_vals = {}
            for i in range(r):
                for j in range(i + 1, r):
                    cnt = sum(1 for u in part_verts[i] for v in part_verts[j] if y[(u, v)] in model)
                    if cnt > 0:
                        E_vals[(i, j)] = cnt
            print(f"[{label}] SAT ({solver_name}) in {t_sol:.2f}s! m={m_vals}, m_in={sum(m_vals)}, m_out={mout}, E={E_vals}", flush=True)
            return "SAT"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True, choices=["controls", "p6", "p7", "p8", "p9"])
    ap.add_argument("--solver", default="cadical195")
    args = ap.parse_args()

    if args.case == "controls":
        r1 = run_solve("NEG-CTRL r=3 (4,3,3)", (4, 3, 3), r=3, trans_parts=[0, 1, 2], solver_name=args.solver)
        assert r1 == "UNSAT", "Negative control FAILED!"
        r2 = run_solve("POS-CTRL r=6 #9 maxE=160", (7, 6, 6, 6, 6, 6), r=6, trans_parts=[0], max_edges_override=160, solver_name=args.solver)
        assert r2 == "SAT", "Positive control FAILED!"
        print("ALL CONTROLS PASSED!", flush=True)
    elif args.case == "p6":
        run_solve("Profile #6 (7,7,7,6,5,5) trans=[0,1,2]", (7, 7, 7, 6, 5, 5), r=6, fixed_m=(5, 5, 5, 0, 0, 0), trans_parts=[0, 1, 2], solver_name=args.solver)
    elif args.case == "p7":
        run_solve("Profile #7 (8,6,6,6,6,5) trans=[0]", (8, 6, 6, 6, 6, 5), r=6, fixed_m=None, trans_parts=[0], solver_name=args.solver)
    elif args.case == "p8":
        run_solve("Profile #8 (7,7,6,6,6,5) trans=[0,1]", (7, 7, 6, 6, 6, 5), r=6, fixed_m=None, trans_parts=[0, 1], solver_name=args.solver)
    elif args.case == "p9":
        run_solve("Profile #9 (7,6,6,6,6,6) trans=[0]", (7, 6, 6, 6, 6, 6), r=6, fixed_m=None, trans_parts=[0], solver_name=args.solver)

if __name__ == "__main__":
    main()
