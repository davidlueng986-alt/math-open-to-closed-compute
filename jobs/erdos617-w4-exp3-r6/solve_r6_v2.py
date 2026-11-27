#!/usr/bin/env python3
"""
Erdos Problem #617 (r=6, K_37) Sharded Exact SAT + CEGAR Solver (v2)
Includes:
  - Min-Defect Local Optimality (zero-var binary clauses)
  - Generalized Property (L)
  - NEW Wave 4 Exact Quadratic Turan-Cauchy-Schwarz Cross-Edge Bound
  - NEW Wave 4 Two-Vertex Color-Coupling Theorem (zero-var binary/ternary clauses)
  - Exact Turan Subset Cross-Edge Bounds (|T| = 2, binding |T| = 3)
  - Sound Vertex Symmetry Breaking (d_miss desc for m_i>0, d(u, A_0) desc for m_i=0)
  - Exact Transversal-No-Alpha7 clauses + Incremental Exact 7-IS CEGAR loop
  - Multiprocessing across defect vectors for fast sharded GitHub Actions execution
"""
import argparse
import math
import multiprocessing as mp
import os
import sys
import time
from itertools import combinations, product


def emin(n, r=6):
    q, rem = divmod(n, r)
    return rem * (q + 1) * q // 2 + (r - rem) * q * (q - 1) // 2


def quad_turan_ub(mi, sj):
    if sj == 0:
        return 0
    return min(sj + mi, (sj + math.isqrt(sj * sj + 8 * mi * sj)) // 2)


class CNFBuilder:
    def __init__(self):
        self.nvars = 0
        self.clauses = []

    def new_var(self):
        self.nvars += 1
        return self.nvars

    def add(self, *lits):
        self.clauses.append(list(lits))

    def totalizer(self, lits, ub):
        """Return list out[0..min(len, ub+1)-1] where out[k] is True if sum(lits) >= k+1."""
        n = len(lits)
        if n == 0 or ub < 0:
            return []
        if n == 1:
            return [lits[0]]
        mid = n // 2
        L = self.totalizer(lits[:mid], ub)
        R = self.totalizer(lits[mid:], ub)
        cap = min(len(L) + len(R), ub + 1)
        out = [self.new_var() for _ in range(cap)]
        for i, l in enumerate(L):
            if i < cap:
                self.add(-l, out[i])
        for j, r_lit in enumerate(R):
            if j < cap:
                self.add(-r_lit, out[j])
        for i, l in enumerate(L):
            for j, r_lit in enumerate(R):
                if i + j + 1 < cap:
                    self.add(-l, -r_lit, out[i + j + 1])
        return out

    def add_at_most_k(self, lits, k):
        if k < 0:
            self.add()  # UNSAT
            return []
        if k >= len(lits):
            return []
        if k == 0:
            for l in lits:
                self.add(-l)
            return []
        if k == 1 and len(lits) <= 6:
            for a, b in combinations(lits, 2):
                self.add(-a, -b)
            return []
        out = self.totalizer(lits, k)
        if len(out) > k:
            self.add(-out[k])
        return out

    def add_at_least_k(self, lits, k):
        if k <= 0:
            return
        if k > len(lits):
            self.add()
            return
        self.add_at_most_k([-l for l in lits], len(lits) - k)

    def add_equals_k(self, lits, k):
        self.add_at_most_k(lits, k)
        self.add_at_least_k(lits, k)


def gen_defect_vectors(parts, r=6, max_total_edges=111):
    mins = [(r - 1) * emin(a, r) for a in parts]
    in_e = sum(a * (a - 1) // 2 for a in parts)
    e_turan = emin(sum(parts), r)
    max_m_in = max_total_edges - e_turan
    res = []

    def rec(idx, rem, cur):
        if idx == r:
            m_in = sum(cur)
            max_mout = max_total_edges - in_e + m_in
            min_mout = 2 * m_in + e_turan - in_e
            if min_mout <= max_mout and max_mout >= 0:
                res.append(tuple(cur))
            return
        hi = rem
        if idx > 0 and parts[idx] == parts[idx - 1]:
            hi = min(hi, cur[-1])
        for v in range(mins[idx], hi + 1):
            rec(idx + 1, rem - v, cur + [v])

    rec(0, max_m_in, [])
    return res


def build_fixed_m_cnf(parts, fixed_m, r=6, max_total_edges=111,
                      trans_parts=None, sym_break=True, use_tvc=True):
    cnf = CNFBuilder()
    N = sum(parts)
    part_verts = []
    cur = 0
    for a in parts:
        part_verts.append(list(range(cur, cur + a)))
        cur += a

    in_e = sum(a * (a - 1) // 2 for a in parts)
    e_turan = emin(N, r)
    m_in = sum(fixed_m)
    max_mout = max_total_edges - in_e + m_in
    min_mout = max(0, 2 * m_in + e_turan - in_e)
    s_vals = [fixed_m[i] - (r - 1) * emin(parts[i], r) for i in range(r)]
    if any(sv < 0 for sv in s_vals) or min_mout > max_mout:
        cnf.add()
        return cnf, {}, {}, part_verts

    # Variables: x[u,v] (missing intra-part edge in G1) for parts with m_i > 0
    x = {}
    for i in range(r):
        if fixed_m[i] == 0:
            continue
        vs = part_verts[i]
        for a_idx in range(len(vs)):
            for b_idx in range(a_idx + 1, len(vs)):
                x[(vs[a_idx], vs[b_idx])] = cnf.new_var()

    # y[u,v] (present cross-part edge in G1)
    y = {}
    for i in range(r):
        for j in range(i + 1, r):
            for u in part_verts[i]:
                for v in part_verts[j]:
                    y[(u, v)] = cnf.new_var()

    # 1. Exact defect counts per part + d_miss totalizers
    dm_tot = {}
    for i in range(r):
        if fixed_m[i] == 0:
            continue
        vs = part_verts[i]
        elits = [x[(vs[a], vs[b])] for a in range(len(vs)) for b in range(a + 1, len(vs))]
        cnf.add_equals_k(elits, fixed_m[i])
        for u in vs:
            inc = [x[(min(u, v), max(u, v))] for v in vs if v != u]
            dm_tot[u] = cnf.totalizer(inc, min(len(inc), fixed_m[i]))

    # 2. Global m_out bounds
    all_y = list(y.values())
    cnf.add_at_most_k(all_y, max_mout)
    if min_mout > 0:
        cnf.add_at_least_k(all_y, min_mout)

    # 3. Per-vertex degree totalizers d(u, A_j), Property (L), Local Optimality, Quadratic Turan-CS
    deg_tot = {}
    for i in range(r):
        for j in range(r):
            if i == j:
                continue
            aj = parts[j]
            kj = aj - r
            sj = s_vals[j]
            ub_deg = aj
            if aj >= r:
                ub_deg = min(ub_deg, kj + 1 + sj)

            excess_lits = []
            for u in part_verts[i]:
                ylits = [y[(min(u, w), max(u, w))] for w in part_verts[j]]
                # Property (L) + degree totalizer
                if ub_deg < aj:
                    out = cnf.add_at_most_k(ylits, ub_deg)
                else:
                    out = cnf.totalizer(ylits, aj)
                deg_tot[(u, j)] = out
                # ZERO-VAR Local optimality: d(u, A_j) + d_miss(u) <= a_j
                if fixed_m[i] > 0:
                    dmu = dm_tot[u]
                    for a in range(len(out)):
                        b = aj - 1 - a
                        if 0 <= b < len(dmu):
                            cnf.add(-out[a], -dmu[b])
                # Collect excess above (kj + 1) for Quadratic Turan-CS
                if aj >= r and sj >= 1:
                    thresh = kj + 1
                    for k_idx in range(thresh, len(out)):
                        excess_lits.append(out[k_idx])

            # NEW Wave 4 Exact Quadratic Turan-Cauchy-Schwarz Cross-Edge Bound
            if aj >= r and sj >= 1 and excess_lits:
                rhs_q = quad_turan_ub(fixed_m[i], sj)
                if rhs_q < len(excess_lits):
                    cnf.add_at_most_k(excess_lits, rhs_q)

            # NEW Wave 4 Two-Vertex Color-Coupling Theorem (ZERO-VAR binary/ternary clauses!)
            if use_tvc and aj >= r and sj >= 1:
                K0 = 2 * kj + 2 + sj
                K1 = K0 + 1
                vs = part_verts[i]
                for a_idx in range(len(vs)):
                    u = vs[a_idx]
                    tu = deg_tot[(u, j)]
                    for b_idx in range(a_idx + 1, len(vs)):
                        v = vs[b_idx]
                        tv = deg_tot[(v, j)]
                        if fixed_m[i] == 0:
                            for a in range(len(tu)):
                                b = K0 - 1 - a
                                if 0 <= b < len(tv):
                                    cnf.add(-tu[a], -tv[b])
                        else:
                            xuv = x[(u, v)]
                            for a in range(len(tu)):
                                b = K0 - 1 - a
                                if 0 <= b < len(tv):
                                    cnf.add(xuv, -tu[a], -tv[b])
                            for a in range(len(tu)):
                                b = K1 - 1 - a
                                if 0 <= b < len(tv):
                                    cnf.add(-tu[a], -tv[b])

    # 4. Exact Turan Subset Cross-Edge Bounds for |T| = 2 and binding |T| = 3
    for sz in (2, 3):
        for T in combinations(range(r), sz):
            NT = sum(parts[i] for i in T)
            prod_sum = sum(parts[i] * parts[j] for i, j in combinations(T, 2))
            rhs = prod_sum - (r - 1) * emin(NT, r) + sum(fixed_m[i] for i in T)
            if rhs < prod_sum and (sz == 2 or rhs <= max_mout - 4):
                lits = []
                for i, j in combinations(T, 2):
                    for u in part_verts[i]:
                        for v in part_verts[j]:
                            lits.append(y[(u, v)])
                cnf.add_at_most_k(lits, rhs)

    # 5. Sound Symmetry Breaking inside each part
    if sym_break:
        for i in range(r):
            vs = part_verts[i]
            if fixed_m[i] > 0:
                for idx in range(len(vs) - 1):
                    for k in range(len(dm_tot[vs[idx]])):
                        cnf.add(-dm_tot[vs[idx + 1]][k], dm_tot[vs[idx]][k])
            else:
                ref = 0 if i != 0 else 1
                for idx in range(len(vs) - 1):
                    t_cur = deg_tot[(vs[idx], ref)]
                    t_nxt = deg_tot[(vs[idx + 1], ref)]
                    for k in range(min(len(t_cur), len(t_nxt))):
                        cnf.add(-t_nxt[k], t_cur[k])

    # 6. Exact Transversal-No-Alpha(r+1) Clauses for i in trans_parts
    if trans_parts is None:
        nz = sorted([i for i in range(r) if fixed_m[i] > 0], key=lambda i: (-fixed_m[i], i))
        trans_parts = nz[:2]
    for i in trans_parts:
        if fixed_m[i] == 0:
            continue
        others = [j for j in range(r) if j != i]
        other_lists = [part_verts[j] for j in others]
        pairs_i = list(combinations(part_verts[i], 2))
        for W in product(*other_lists):
            tW = cnf.new_var()
            cl_t = [tW]
            for a_idx in range(len(others)):
                for b_idx in range(a_idx + 1, len(others)):
                    u, v = W[a_idx], W[b_idx]
                    cl_t.append(y[(min(u, v), max(u, v))])
            cnf.add(*cl_t)
            for u, v in pairs_i:
                cl = [-x[(u, v)], -tW]
                for w in W:
                    cl.append(y[(min(u, w), max(u, w))])
                    cl.append(y[(min(v, w), max(v, w))])
                cnf.add(*cl)

    return cnf, x, y, part_verts


def find_independent_sets_r_plus_1(N, adj_mask, target_size, max_found=200):
    """Exact bitmask backtracking to find independent sets of size target_size in G1."""
    found = []
    full = (1 << N) - 1

    def bt(chosen, cand_mask, need):
        if len(found) >= max_found:
            return
        if need == 0:
            found.append(tuple(chosen))
            return
        if cand_mask.bit_count() < need:
            return
        m = cand_mask
        while m:
            lsb = m & -m
            v = lsb.bit_length() - 1
            m ^= lsb
            if (m | lsb).bit_count() < need:
                break
            chosen.append(v)
            bt(chosen, m & ~adj_mask[v], need - 1)
            chosen.pop()
            if len(found) >= max_found:
                return

    bt([], full, target_size)
    return found


def solve_one_vector(args):
    parts, fixed_m, r, max_total_edges, solver_name, sym_break, use_tvc, trans_mode = args
    from pysat.solvers import Solver

    t0 = time.time()
    nz = sorted([i for i in range(r) if fixed_m[i] > 0], key=lambda i: (-fixed_m[i], i))
    if trans_mode == "all":
        tp = nz
    elif trans_mode == "top1":
        tp = nz[:1]
    else:
        tp = nz[:2]

    cnf, x, y, part_verts = build_fixed_m_cnf(
        parts, fixed_m, r=r, max_total_edges=max_total_edges,
        trans_parts=tp, sym_break=sym_break, use_tvc=use_tvc
    )
    N = sum(parts)
    vert_part = {}
    for i, vs in enumerate(part_verts):
        for v in vs:
            vert_part[v] = i

    rounds = 0
    total_cuts = 0
    with Solver(name=solver_name, bootstrap_with=cnf.clauses) as s:
        while True:
            rounds += 1
            sat = s.solve()
            if not sat:
                dt = time.time() - t0
                return ("UNSAT", fixed_m, dt, rounds, total_cuts, cnf.nvars, len(cnf.clauses), None)
            model = set(l for l in s.get_model() if l > 0)
            adj = [0] * N
            for i in range(r):
                vs = part_verts[i]
                for a_idx in range(len(vs)):
                    u = vs[a_idx]
                    for b_idx in range(a_idx + 1, len(vs)):
                        v = vs[b_idx]
                        if fixed_m[i] == 0 or (x[(u, v)] not in model):
                            adj[u] |= (1 << v)
                            adj[v] |= (1 << u)
            for (u, v), var in y.items():
                if var in model:
                    adj[u] |= (1 << v)
                    adj[v] |= (1 << u)

            iss = find_independent_sets_r_plus_1(N, adj, r + 1, max_found=200)
            if not iss:
                dt = time.time() - t0
                e_cnt = sum(m.bit_count() for m in adj) // 2
                return ("SAT_VALID_G1", fixed_m, dt, rounds, total_cuts, cnf.nvars, len(cnf.clauses), (e_cnt, adj))

            for S in iss:
                cl = []
                for a_idx in range(len(S)):
                    u = S[a_idx]
                    for b_idx in range(a_idx + 1, len(S)):
                        v = S[b_idx]
                        p1, p2 = vert_part[u], vert_part[v]
                        if p1 == p2:
                            if fixed_m[p1] > 0:
                                cl.append(-x[(min(u, v), max(u, v))])
                        else:
                            cl.append(y[(min(u, v), max(u, v))])
                s.add_clause(cl)
                total_cuts += 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--profile", required=True, choices=["controls", "p6", "p7", "p8", "p9"])
    ap.add_argument("--solver", default="cadical195")
    ap.add_argument("--shard-idx", type=int, default=0)
    ap.add_argument("--num-shards", type=int, default=1)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--trans-mode", default="top2", choices=["top1", "top2", "all"])
    ap.add_argument("--no-sym-break", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if args.profile == "controls":
        vecs_r3 = gen_defect_vectors((4, 3, 3), r=3, max_total_edges=15)
        print(f"[CTRL r=3 (4,3,3)] {len(vecs_r3)} defect vectors: {vecs_r3}", flush=True)
        if args.dry_run:
            return
        for fm in vecs_r3:
            res = solve_one_vector(((4, 3, 3), fm, 3, 15, args.solver, not args.no_sym_break, True, "all"))
            print(f"  r=3 {fm}: {res[0]} in {res[2]:.3f}s (rounds={res[3]}, cuts={res[4]})", flush=True)
            assert res[0] == "UNSAT", f"Negative control failed on {fm}!"
        res_pos = solve_one_vector(((5, 4, 4, 4), (3, 3, 3, 0), 4, 60, args.solver, not args.no_sym_break, True, "all"))
        print(f"[POS-CTRL r=4 (5,4,4,4) maxE=60] {res_pos[0]} in {res_pos[2]:.3f}s (rounds={res_pos[3]}, cuts={res_pos[4]})", flush=True)
        assert res_pos[0] == "SAT_VALID_G1", "Positive control failed!"
        print("CONTROLS PASSED!", flush=True)
        return

    PROFILES = {
        "p6": (7, 7, 7, 6, 5, 5),
        "p7": (8, 6, 6, 6, 6, 5),
        "p8": (7, 7, 6, 6, 6, 5),
        "p9": (7, 6, 6, 6, 6, 6),
    }
    parts = PROFILES[args.profile]
    vecs = gen_defect_vectors(parts, r=6, max_total_edges=111)
    vecs.sort(key=lambda v: (sum(v), v))
    my_vecs = [v for idx, v in enumerate(vecs) if idx % args.num_shards == args.shard_idx]
    print(f"[{args.profile} {parts}] total_vecs={len(vecs)}, shard {args.shard_idx}/{args.num_shards} -> {len(my_vecs)} vecs, solver={args.solver}, workers={args.workers}", flush=True)

    if args.dry_run:
        if my_vecs:
            cnf, _, _, _ = build_fixed_m_cnf(parts, my_vecs[-1], sym_break=not args.no_sym_break)
            print(f"  Sample hardest vec {my_vecs[-1]}: {cnf.nvars} vars, {len(cnf.clauses)} clauses")
        return

    tasks = [
        (parts, fm, 6, 111, args.solver, not args.no_sym_break, True, args.trans_mode)
        for fm in my_vecs
    ]
    t_start = time.time()
    n_unsat = 0
    n_sat = 0
    with mp.Pool(processes=min(args.workers, max(1, len(tasks)))) as pool:
        for res in pool.imap_unordered(solve_one_vector, tasks):
            status, fm, dt, rounds, cuts, nv, nc, extra = res
            if status == "UNSAT":
                n_unsat += 1
            else:
                n_sat += 1
            print(f"[{args.profile}] {fm} -> {status} in {dt:.2f}s (rounds={rounds}, cuts={cuts}, {nv}v/{nc}c) [{n_unsat+n_sat}/{len(tasks)}]", flush=True)
            if status == "SAT_VALID_G1":
                e_cnt, adj = extra
                print(f"  *** FOUND VALID G1 with alpha(G1)<=6! |E(G1)|={e_cnt}, adj={adj} ***", flush=True)

    print(f"[{args.profile} shard {args.shard_idx}/{args.num_shards}] FINISHED in {time.time()-t_start:.2f}s: UNSAT={n_unsat}, SAT_VALID_G1={n_sat}", flush=True)


if __name__ == "__main__":
    main()
