import json, math, sys, time
from itertools import combinations, product
from math import comb, lcm
from scipy.optimize import linprog
import numpy as np
from ortools.sat.python import cp_model

def e_min(n, r=6):
    q, rem = divmod(n, r)
    return rem * comb(q + 1, 2) + (r - rem) * comb(q, 2)

def k_ub(a_j, s_j):
    if a_j == 6: return min(2 * (1 + s_j), 3 + s_j, 6)
    if a_j == 7: return min(2 * (2 + s_j), 5 + s_j, 7)
    if a_j == 8: return min(2 * (3 + s_j), 7 + s_j, 8)
    if a_j == 5: return min(6 + s_j, 5)
    raise ValueError(a_j)

def delta_ub(a_j, s_j):
    return min(a_j, (a_j - 5) + s_j) if a_j >= 6 else 5

def min_E_for_b_subset_dc(sizes_sub, m_sub, b):
    if any(x <= 0 for x in b): return 0
    r = len(sizes_sub)
    if r <= 1: return None
    s_sub = [m_sub[j] - 5 * e_min(sizes_sub[j], 6) for j in range(r)]
    deltas = [delta_ub(sizes_sub[j], s_sub[j]) for j in range(r)]
    pairs = []
    for j in range(r):
        for l in range(j + 1, r):
            turan_cap = sizes_sub[j] * sizes_sub[l] - 5 * e_min(sizes_sub[j] + sizes_sub[l], 6) + m_sub[j] + m_sub[l]
            dc_cap = min(turan_cap, b[j] * deltas[l], b[l] * deltas[j])
            pairs.append((b[j] * b[l], dc_cap))
    pairs.sort()
    need = 1.0
    used = 0
    for denom, cap in pairs:
        if need <= 1e-12: break
        if cap <= 0: continue
        if cap * (1.0 / denom) >= need - 1e-12:
            used += math.ceil(need * denom - 1e-12)
            need = 0.0
            break
        used += cap
        need -= cap / denom
    return used if need <= 1e-12 else None

plane_cache = {}
def get_dc_planes_for_subset(sizes_sub, m_sub, k_mult=2):
    key = (tuple(sizes_sub), tuple(m_sub), k_mult)
    if key in plane_cache: return plane_cache[key]
    r = len(sizes_sub)
    if r <= 1:
        plane_cache[key] = ([], [], 0)
        return ([], [], 0)
    s_sub = [m_sub[j] - 5 * e_min(sizes_sub[j], 6) for j in range(r)]
    if k_mult == 2:
        ubs = [min(k_ub(sizes_sub[j], s_sub[j]), sizes_sub[j] - 1) for j in range(r)]
    else:
        ubs = [min(k_mult * delta_ub(sizes_sub[j], s_sub[j]), sizes_sub[j] - 1) for j in range(r)]
    all_pts = list(product(*[range(u + 1) for u in ubs]))
    feas_pts, feas_vals = [], []
    for k_pt in all_pts:
        b = [sizes_sub[j] - k_pt[j] for j in range(r)]
        v = min_E_for_b_subset_dc(sizes_sub, m_sub, b)
        if v is not None:
            feas_pts.append(k_pt)
            feas_vals.append(v)
    if not feas_pts:
        plane_cache[key] = ([], [], 0)
        return ([], [], 0)

    k_planes, seen_k = [], set()
    for j in range(r):
        mn = min(pt[j] for pt in feas_pts)
        if mn > 0:
            cs = tuple(1 if idx == j else 0 for idx in range(r))
            if (mn, cs) not in seen_k:
                seen_k.add((mn, cs)); k_planes.append((mn, list(cs)))
    mn_sum = min(sum(pt) for pt in feas_pts)
    if mn_sum > 0:
        cs = tuple([1] * r)
        if (mn_sum, cs) not in seen_k:
            seen_k.add((mn_sum, cs)); k_planes.append((mn_sum, list(cs)))
    for sz in range(2, r):
        for sub in combinations(range(r), sz):
            mn_sub = min(sum(pt[j] for j in sub) for pt in feas_pts)
            if mn_sub > 0:
                cs = tuple(1 if idx in sub else 0 for idx in range(r))
                if (mn_sub, cs) not in seen_k:
                    seen_k.add((mn_sub, cs)); k_planes.append((mn_sub, list(cs)))

    E_planes = []
    min_v = min(feas_vals)
    if min_v > 0: E_planes.append((1, min_v, [0] * r))
    A_ub = np.array([[1.0] + [-float(x) for x in k] for k in feas_pts])
    b_ub = np.array(feas_vals, dtype=float)
    targets = [[0]*r, [min(1,u) for u in ubs], [min(2,u) for u in ubs], [u//2 for u in ubs], [u for u in ubs]]
    seen = set()
    for tgt in targets:
        res = linprog([-1.0] + [float(x) for x in tgt], A_ub=A_ub, b_ub=b_ub, bounds=[(0, None)]*(r+1), method="highs")
        if res.success:
            D = 60
            cs = [int(round(res.x[j+1] * D)) for j in range(r)]
            c0 = min(D * feas_vals[idx] + sum(cs[j]*feas_pts[idx][j] for j in range(r)) for idx in range(len(feas_pts)))
            if c0 > 0:
                g = math.gcd(D, c0, *cs)
                plane = (D//g, c0//g, tuple(x//g for x in cs))
                if plane not in seen:
                    seen.add(plane); E_planes.append((plane[0], plane[1], list(plane[2])))
    plane_cache[key] = (E_planes, k_planes, len(feas_pts))
    return plane_cache[key]

RT_EXCESS = {(2, 13): 1, (2, 14): 2, (2, 15): 3, (3, 19): 2, (3, 20): 3}
DEG_EDGE_RHS = {12: 42, 13: 45, 14: 49, 19: 74, 20: 79}

def check_mvec(sizes, m_vec, time_limit=15.0, workers=4, max_rounds=40):
    t_start = time.time()
    k = len(sizes)
    parts, cur = [], 0
    for sz in sizes:
        parts.append(list(range(cur, cur + sz))); cur += sz

    sum_c = sum(comb(sz, 2) for sz in sizes)
    min_m = [5 * e_min(sz, 6) for sz in sizes]
    s_vec = [m_vec[i] - min_m[i] for i in range(k)]
    deltas = [delta_ub(sizes[i], s_vec[i]) for i in range(k)]
    m_in = sum(m_vec)
    max_mout = 111 - sum_c + m_in

    model = cp_model.CpModel()
    miss, mdeg_vars = {}, {}
    for i, P in enumerate(parts):
        if m_vec[i] > 0:
            for u, v in combinations(P, 2):
                miss[(i, u, v)] = model.NewBoolVar(f"m_{i}_{u}_{v}")
            model.Add(sum(miss[(i, u, v)] for u, v in combinations(P, 2)) == m_vec[i])
            mdegs = []
            for u in P:
                dm = model.NewIntVar(0, sizes[i] - 1, f"dm_{u}")
                model.Add(dm == sum(miss[(i, min(u, v), max(u, v))] for v in P if v != u))
                mdegs.append(dm); mdeg_vars[u] = dm
            for idx in range(len(P) - 1):
                model.Add(mdegs[idx] >= mdegs[idx + 1])
        else:
            for u in P: mdeg_vars[u] = 0

    d = {}
    for i, P in enumerate(parts):
        for v in P:
            for j in range(k):
                if j == i: continue
                d[(v, j)] = model.NewIntVar(0, deltas[j], f"d_{v}_{j}")

    E = {}
    for i in range(k):
        for j in range(i + 1, k):
            cap = sizes[i] * sizes[j] - 5 * e_min(sizes[i] + sizes[j], 6) + m_vec[i] + m_vec[j]
            eij = model.NewIntVar(0, min(cap, max_mout), f"E_{i}_{j}")
            model.Add(eij == sum(d[(v, j)] for v in parts[i]))
            model.Add(eij == sum(d[(v, i)] for v in parts[j]))
            E[(i, j)] = eij

    def get_E(a, b): return E[(min(a, b), max(a, b))]

    for i in range(k - 1):
        if sizes[i] == sizes[i + 1] and m_vec[i] == m_vec[i + 1]:
            e_tot_i = sum(get_E(i, j) for j in range(k) if j != i)
            e_tot_i1 = sum(get_E(i + 1, j) for j in range(k) if j != i + 1)
            model.Add(e_tot_i >= e_tot_i1)

    for i, P in enumerate(parts):
        if m_vec[i] == 0:
            tots = [sum(d[(v, j)] for j in range(k) if j != i) for v in P]
            for idx in range(len(P) - 1):
                model.Add(tots[idx] >= tots[idx + 1])

    m_out = model.NewIntVar(0, max_mout, "m_out")
    model.Add(m_out == sum(E.values()))
    e_g1 = sum_c - m_in + m_out
    model.Add(m_in <= e_g1 - 96)

    for i, P in enumerate(parts):
        if m_vec[i] > 0:
            for v in P:
                for j in range(k):
                    if j == i: continue
                    model.Add(sizes[j] - d[(v, j)] >= mdeg_vars[v])

    for r_sz in range(3, k + 1):
        for T in combinations(range(k), r_sz):
            nt = sum(sizes[i] for i in T)
            cross_max = sum(sizes[i] * sizes[j] for i, j in combinations(T, 2))
            rhs = cross_max - 5 * e_min(nt, 6) + sum(m_vec[i] for i in T)
            model.Add(sum(E[(i, j)] for i, j in combinations(T, 2)) <= rhs)

    for r_sz in (2, 3):
        for S_sub in combinations(range(k), r_sz):
            nt = sum(sizes[i] for i in S_sub)
            if nt not in DEG_EDGE_RHS: continue
            rhs_de = DEG_EDGE_RHS[nt]
            e_in_S = sum(comb(sizes[i], 2) - m_vec[i] for i in S_sub)
            E_S = sum(E[(i, j)] for i, j in combinations(S_sub, 2))
            for i in S_sub:
                other_S = [j for j in S_sub if j != i]
                for v in parts[i]:
                    d_v_S = (sizes[i] - 1) - mdeg_vars[v] + sum(d[(v, j)] for j in other_S)
                    model.Add(d_v_S + e_in_S + E_S <= rhs_de)

    for i in range(k):
        ai = sizes[i]
        c2 = 2 * ai - 5 * e_min(ai + 2, 6) + m_vec[i]
        if ai >= 6:
            thresh = ai - 5
            for j in range(k):
                if j == i: continue
                exc = []
                for x in parts[j]:
                    ex = model.NewIntVar(0, ai, f"ex_{x}_{i}")
                    model.Add(ex >= d[(x, i)] - thresh)
                    exc.append(ex)
                model.Add(sum(exc) <= s_vec[i] + m_vec[j])
        for j in range(k):
            if j == i: continue
            for u, v in combinations(parts[j], 2):
                if m_vec[j] > 0:
                    model.Add(d[(u, i)] + d[(v, i)] <= c2 + miss[(j, u, v)])
                else:
                    model.Add(d[(u, i)] + d[(v, i)] <= c2)

    for i, P in enumerate(parts):
        if sizes[i] == 8:
            for u in P: model.Add(mdeg_vars[u] <= m_vec[i] - 5)

    azh_map = {}
    for i, P in enumerate(parts):
        if m_vec[i] == 0: continue
        other = [j for j in range(k) if j != i]
        Z = [j for j in other if sizes[j] == 6 and m_vec[j] == 0]
        R = [j for j in other if j not in Z]

        E_pl_all, k_pl_all, feas_all = get_dc_planes_for_subset([sizes[j] for j in other], [m_vec[j] for j in other], 2)
        E_rest_all = sum(get_E(j, l) for j, l in combinations(other, 2))
        can_dom_all = [j for j in other if k_ub(sizes[j], s_vec[j]) >= sizes[j]]

        E_pl_R, k_pl_R, feas_R = get_dc_planes_for_subset([sizes[j] for j in R], [m_vec[j] for j in R], 2) if len(R) >= 2 else ([], [], 0)
        E_rest_R = sum(get_E(j, l) for j, l in combinations(R, 2)) if len(R) >= 2 else 0
        can_dom_R = [j for j in R if k_ub(sizes[j], s_vec[j]) >= sizes[j]]

        for u, v in combinations(P, 2):
            dom_map = {}
            for j in can_dom_all:
                dom = model.NewBoolVar(f"dom_{u}_{v}_{j}")
                model.Add(d[(u, j)] + d[(v, j)] >= sizes[j]).OnlyEnforceIf(dom)
                model.Add(d[(u, j)] + d[(v, j)] <= sizes[j] - 1).OnlyEnforceIf(dom.Not())
                dom_map[j] = dom

            conds_all = [miss[(i, u, v)]] + [dom_map[j].Not() for j in can_dom_all]
            if feas_all == 0:
                model.AddBoolOr([c.Not() for c in conds_all])
            else:
                for c0, cs in k_pl_all:
                    terms = [cs[idx] * (d[(u, other[idx])] + d[(v, other[idx])]) for idx in range(5) if cs[idx] != 0]
                    model.Add(sum(terms) >= c0).OnlyEnforceIf(conds_all)
                for D, c0, cs in E_pl_all:
                    terms = [cs[idx] * (d[(u, other[idx])] + d[(v, other[idx])]) for idx in range(5) if cs[idx] != 0]
                    rhs = c0 - sum(terms) if terms else c0
                    model.Add(D * E_rest_all >= rhs).OnlyEnforceIf(conds_all)

            if len(Z) >= 1:
                all_Z_hit = model.NewBoolVar(f"azh_{i}_{u}_{v}")
                model.Add(sum(d[(u, j)] + d[(v, j)] for j in Z) == 2 * len(Z)).OnlyEnforceIf(all_Z_hit)
                model.Add(sum(d[(u, j)] + d[(v, j)] for j in Z) <= 2 * len(Z) - 1).OnlyEnforceIf(all_Z_hit.Not())
                azh_map[(i, u, v)] = all_Z_hit
                if len(R) <= 1:
                    if len(R) == 1 and R[0] in dom_map:
                        model.AddBoolOr([miss[(i, u, v)].Not(), all_Z_hit, dom_map[R[0]]])
                    else:
                        model.AddImplication(miss[(i, u, v)], all_Z_hit)
                else:
                    conds_R = [miss[(i, u, v)], all_Z_hit.Not()] + [dom_map[j].Not() for j in can_dom_R]
                    if feas_R == 0:
                        model.AddBoolOr([c.Not() for c in conds_R])
                    else:
                        for c0, cs in k_pl_R:
                            terms = [cs[idx] * (d[(u, R[idx])] + d[(v, R[idx])]) for idx in range(len(R)) if cs[idx] != 0]
                            model.Add(sum(terms) >= c0).OnlyEnforceIf(conds_R)
                        for D, c0, cs in E_pl_R:
                            terms = [cs[idx] * (d[(u, R[idx])] + d[(v, R[idx])]) for idx in range(len(R)) if cs[idx] != 0]
                            rhs = c0 - sum(terms) if terms else c0
                            model.Add(D * E_rest_R >= rhs).OnlyEnforceIf(conds_R)
                        if len(R) == 2:
                            p, q = R[0], R[1]
                            bp = model.NewIntVar(0, sizes[p], f"bp_{u}_{v}_{p}")
                            bq = model.NewIntVar(0, sizes[q], f"bq_{u}_{v}_{q}")
                            model.Add(bp == sizes[p] - d[(u, p)] - d[(v, p)]).OnlyEnforceIf(conds_R)
                            model.Add(bq == sizes[q] - d[(u, q)] - d[(v, q)]).OnlyEnforceIf(conds_R)
                            prod_pq = model.NewIntVar(0, sizes[p] * sizes[q], f"pr_{u}_{v}_{p}_{q}")
                            model.AddMultiplicationEquality(prod_pq, [bp, bq])
                            model.Add(get_E(p, q) >= prod_pq).OnlyEnforceIf(conds_R)

    for s_sz in (2, 3):
        for S_sub in combinations(range(k), s_sz):
            nt = sum(sizes[i] for i in S_sub)
            if (s_sz, nt) not in RT_EXCESS: continue
            delta_rt = RT_EXCESS[(s_sz, nt)]
            W = [p for p in range(k) if p not in S_sub]
            cross_max = sum(sizes[i] * sizes[j] for i, j in combinations(S_sub, 2))
            rt_ub = cross_max - 5 * (e_min(nt, 6) + delta_rt) + sum(m_vec[i] for i in S_sub)
            E_S = sum(E[(i, j)] for i, j in combinations(S_sub, 2))

            has_Q = model.NewBoolVar(f"rtQ_{S_sub}")
            model.Add(E_S <= rt_ub).OnlyEnforceIf(has_Q.Not())
            dp_vars, dom_W = {}, []
            for p in W:
                max_dp = min(sizes[p], (s_sz + 1) * deltas[p])
                dp = model.NewIntVar(0, max_dp, f"rtd_{S_sub}_{p}")
                E_U_p = sum(get_E(i, p) for i in S_sub)
                model.Add(dp <= E_U_p).OnlyEnforceIf(has_Q)
                dp_vars[p] = dp
                if max_dp >= sizes[p]:
                    dw = model.NewBoolVar(f"rtdw_{S_sub}_{p}")
                    model.Add(dp >= sizes[p]).OnlyEnforceIf(dw)
                    model.Add(dp <= sizes[p] - 1).OnlyEnforceIf(dw.Not())
                    dom_W.append(dw)
            conds_W = [has_Q] + [dw.Not() for dw in dom_W]
            E_pl_W, k_pl_W, feas_W = get_dc_planes_for_subset([sizes[p] for p in W], [m_vec[p] for p in W], s_sz + 1)
            if feas_W == 0:
                model.AddBoolOr([c.Not() for c in conds_W])
            else:
                E_W = sum(get_E(p, q) for p, q in combinations(W, 2))
                for c0, cs in k_pl_W:
                    terms = [cs[idx] * dp_vars[W[idx]] for idx in range(len(W)) if cs[idx] != 0]
                    model.Add(sum(terms) >= c0).OnlyEnforceIf(conds_W)
                for D, c0, cs in E_pl_W:
                    terms = [cs[idx] * dp_vars[W[idx]] for idx in range(len(W)) if cs[idx] != 0]
                    rhs = c0 - sum(terms) if terms else c0
                    model.Add(D * E_W >= rhs).OnlyEnforceIf(conds_W)

    added_cuts = set()
    for rnd in range(max_rounds):
        rem = time_limit - (time.time() - t_start)
        if rem <= 0.1:
            return "UNKNOWN", rnd, round(time.time() - t_start, 2)
        solver = cp_model.CpSolver()
        solver.parameters.num_search_workers = workers
        solver.parameters.max_time_in_seconds = rem
        status = solver.Solve(model)
        if status == cp_model.INFEASIBLE:
            return "INFEASIBLE", rnd, round(time.time() - t_start, 2)
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            return solver.StatusName(status), rnd, round(time.time() - t_start, 2)

        E_val = {(a, b): solver.Value(E[(a, b)]) for (a, b) in E}
        def gEv(a, b): return E_val[(min(a, b), max(a, b))]

        new_cuts = 0
        for i, P in enumerate(parts):
            if m_vec[i] == 0: continue
            other = [j for j in range(k) if j != i]
            Z = [j for j in other if sizes[j] == 6 and m_vec[j] == 0]
            R = [j for j in other if j not in Z]

            for u, v in combinations(P, 2):
                if solver.Value(miss[(i, u, v)]) == 0: continue
                subsets_to_check = [(other, False)]
                if len(Z) >= 1 and solver.Value(azh_map[(i, u, v)]) == 0 and len(R) >= 2:
                    subsets_to_check.append((R, True))
                for sub, is_R in subsets_to_check:
                    ks = tuple(solver.Value(d[(u, j)]) + solver.Value(d[(v, j)]) for j in sub)
                    bs = tuple(sizes[j] - ks[idx] for idx, j in enumerate(sub))
                    if any(b <= 0 for b in bs): continue
                    lhs = 0.0
                    for idx1 in range(len(sub)):
                        for idx2 in range(idx1 + 1, len(sub)):
                            p, q = sub[idx1], sub[idx2]
                            bp, bq = bs[idx1], bs[idx2]
                            cap_pq = min(gEv(p, q), bp * deltas[q], bq * deltas[p])
                            lhs += cap_pq / (bp * bq)
                    if lhs < 1.0 - 1e-9:
                        cut_key = (i, is_R, ks)
                        if cut_key in added_cuts: continue
                        added_cuts.add(cut_key)
                        new_cuts += 1
                        L = 1
                        for idx1 in range(len(sub)):
                            for idx2 in range(idx1 + 1, len(sub)):
                                L = lcm(L, bs[idx1] * bs[idx2])
                        terms = []
                        for idx1 in range(len(sub)):
                            for idx2 in range(idx1 + 1, len(sub)):
                                p, q = sub[idx1], sub[idx2]
                                bp, bq = bs[idx1], bs[idx2]
                                dc_c = min(bp * deltas[q], bq * deltas[p])
                                coef = L // (bp * bq)
                                epq = get_E(p, q)
                                if dc_c < sizes[p] * sizes[q]:
                                    ec = model.NewIntVar(0, dc_c, f"ec_{rnd}_{i}_{is_R}_{p}_{q}")
                                    model.Add(ec <= epq)
                                    terms.append(coef * ec)
                                else:
                                    terms.append(coef * epq)
                        for u2, v2 in combinations(P, 2):
                            le_flags = []
                            for idx, j in enumerate(sub):
                                fl = model.NewBoolVar(f"le_{rnd}_{i}_{is_R}_{u2}_{v2}_{j}")
                                model.Add(d[(u2, j)] + d[(v2, j)] <= ks[idx]).OnlyEnforceIf(fl)
                                model.Add(d[(u2, j)] + d[(v2, j)] >= ks[idx] + 1).OnlyEnforceIf(fl.Not())
                                le_flags.append(fl)
                            conds = [miss[(i, u2, v2)]] + le_flags
                            if is_R: conds.append(azh_map[(i, u2, v2)].Not())
                            model.Add(sum(terms) >= L).OnlyEnforceIf(conds)
        if new_cuts == 0:
            return "SAT_EXACT_DCPTB", rnd, round(time.time() - t_start, 2)
    return "MAX_ROUNDS", max_rounds, round(time.time() - t_start, 2)

def enum_m_vecs(sizes):
    k = len(sizes)
    min_m = [5 * e_min(sz, 6) for sz in sizes]
    slack = 15 - sum(min_m)
    res = []
    def rec(idx, rem, cur):
        if idx == k:
            res.append(tuple(min_m[i] + cur[i] for i in range(k)))
            return
        hi = rem
        if idx > 0 and sizes[idx] == sizes[idx - 1]:
            hi = min(hi, cur[idx - 1])
        for v in range(hi, -1, -1):
            rec(idx + 1, rem - v, cur + [v])
    rec(0, slack, [])
    return res

if __name__ == "__main__":
    prof = sys.argv[1]
    shard_idx = int(sys.argv[2])
    num_shards = int(sys.argv[3])
    tl1 = float(sys.argv[4]) if len(sys.argv) > 4 else 12.0
    tl2 = float(sys.argv[5]) if len(sys.argv) > 5 else 40.0

    profiles = {
        "7": (8, 6, 6, 6, 6, 5),
        "8": (7, 7, 6, 6, 6, 5),
        "9": (7, 6, 6, 6, 6, 6),
    }
    sizes = profiles[prof]
    all_vecs = enum_m_vecs(sizes)
    my_vecs = [v for idx, v in enumerate(all_vecs) if idx % num_shards == shard_idx]
    print(f"Profile #{prof} {sizes} shard {shard_idx}/{num_shards}: {len(my_vecs)}/{len(all_vecs)} m-vectors", flush=True)

    t0 = time.time()
    results = {}
    retry_list = []
    for mv in my_vecs:
        st, rnd, dt = check_mvec(sizes, mv, time_limit=tl1, workers=4)
        results[str(mv)] = [st, rnd, dt]
        print(f"  S1 {mv}: {st} (rnd={rnd}, {dt}s)", flush=True)
        if st == "UNKNOWN":
            retry_list.append(mv)

    # Stage 2 deeper pass on UNKNOWNs within 600s budget
    for mv in retry_list:
        if time.time() - t0 > 600:
            break
        st, rnd, dt = check_mvec(sizes, mv, time_limit=tl2, workers=4)
        results[str(mv)] = [st, rnd, dt]
        print(f"  S2 {mv}: {st} (rnd={rnd}, {dt}s)", flush=True)

    counts = {}
    survivors = []
    for mv_s, (st, rnd, dt) in results.items():
        counts[st] = counts.get(st, 0) + 1
        if st != "INFEASIBLE":
            survivors.append({"m_vec": mv_s, "status": st, "rnd": rnd, "time": dt})

    summary = {
        "profile": prof,
        "shard": f"{shard_idx}/{num_shards}",
        "total": len(my_vecs),
        "counts": counts,
        "elapsed": round(time.time() - t0, 1),
        "survivors": survivors,
    }
    print("FINAL_SUMMARY_JSON:" + json.dumps(summary), flush=True)
