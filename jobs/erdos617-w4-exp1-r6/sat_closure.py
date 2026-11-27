#!/usr/bin/env python3
"""
Exact incremental CaDiCaL 1.9.5 CEGAR SAT solver for Erdős Problem #617 (r=6, K_37).
Handles:
  - 2-pure-K6 reduction (25-vertex W, Phi(W) = e_out(W) + sum_v w_v * u5[v] + has_u5 <= budget)
  - 1-pure-K6 reduction (31-vertex W1, Phi1(W1) = e_out(W1) + sum_v w_v * u6[v] <= budget)
Every constraint encoded is 100% mathematically necessary (PROVED in Wave 1-4).
Includes built-in positive control verification.
"""
import argparse, itertools, json, sys, time
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType

def e_min(N, r=6):
    q, rem = divmod(N, r)
    return rem * (q + 1) * q // 2 + (r - rem) * q * (q - 1) // 2

def find_violated_is_k(adj, u_val, n, k, max_found=80):
    """Find diverse k-independent sets I in adj where at least one v in I has u_val[v] == 0."""
    comp = [((1 << n) - 1) ^ adj[v] ^ (1 << v) for v in range(n)]
    zero_mask = 0
    for v in range(n):
        if u_val[v] == 0:
            zero_mask |= (1 << v)
    if zero_mask == 0:
        return []

    found = []
    # To get diverse cuts, try starting from different vertices with u_val == 0
    zero_verts = [v for v in range(n) if u_val[v] == 0]
    seen = set()

    def rec(cur, cand, need):
        if len(found) >= max_found:
            return
        if need == 0:
            t = tuple(sorted(cur))
            if t not in seen:
                seen.add(t)
                found.append(t)
            return
        if cand.bit_count() < need:
            return
        c = cand
        while c:
            lsb = c & -c
            v = lsb.bit_length() - 1
            c ^= lsb
            cand ^= lsb
            nc = cand & comp[v]
            if nc.bit_count() >= need - 1:
                cur.append(v)
                rec(cur, nc, need - 1)
                cur.pop()
                if len(found) >= max_found:
                    return
            if cand.bit_count() < need:
                return

    per_start = max(2, max_found // max(1, len(zero_verts)))
    for v0 in zero_verts:
        target = min(max_found, len(found) + per_start)
        old_max = max_found
        max_found = target
        rec([v0], comp[v0], k - 1)
        max_found = old_max
        if len(found) >= max_found:
            break
    return found

def solve_reduced(case_id, part_sizes, m_bounds, u_weights, k_is, budget,
                  require_no_k6_parts=(), has_ab_bonus=True, m_in_exact=None,
                  time_limit=180.0, use_turan_no_u=True, t_no_u_bound=66):
    """
    part_sizes: list of part sizes summing to n (25 for 2K6, 31 for 1K6)
    m_bounds: list of (m_min, m_max) for each part
    u_weights: list of int weight in Phi for each vertex v in 0..n-1 (2 for 2K6, 1 for 1K6, or 0/1 for special vertices)
    k_is: 5 for 2K6, 6 for 1K6
    budget: upper bound on Phi = e_out + sum_v u_weights[v]*u[v] + (has_u if has_ab_bonus else 0)
    """
    t0 = time.time()
    n = sum(part_sizes)
    P = len(part_sizes)
    parts = []
    idx = 0
    v_part = [0] * n
    for p, sz in enumerate(part_sizes):
        pts = list(range(idx, idx + sz))
        parts.append(pts)
        for v in pts:
            v_part[v] = p
        idx += sz

    top_id = 0
    def new_var():
        nonlocal top_id
        top_id += 1
        return top_id

    # Edge variables x[(u,v)] for u < v: True iff edge in G1
    x = {}
    for u in range(n):
        for v in range(u + 1, n):
            x[(u, v)] = new_var()
    def edge(u, v):
        return x[(u, v)] if u < v else x[(v, u)]

    # u_var[v]: True iff v is in U_{k_is}(W)
    u_var = [new_var() for _ in range(n)]
    has_u = new_var()

    clauses = []
    # has_u <-> OR_v u_var[v]
    for v in range(n):
        clauses.append([-u_var[v], has_u])
    clauses.append([-has_u] + u_var)

    # If has_u, at least k_is vertices have u_var[v] = True
    # Encode: has_u -> sum(u_var) >= k_is, i.e., sum(~u_var) <= n - k_is if has_u
    cnf_ge = CardEnc.atmost([-v for v in u_var], bound=n - k_is, top_id=top_id, encoding=EncType.totalizer)
    top_id = max(top_id, cnf_ge.nv)
    for cl in cnf_ge.clauses:
        clauses.append([-has_u] + cl)

    # Internal non-edge variables y = -x inside each part
    all_y = []
    part_y = []
    for p in range(P):
        pts = parts[p]
        ys = [-edge(u, v) for u in pts for v in pts if u < v]
        part_y.append(ys)
        all_y.extend(ys)
        mmin, mmax = m_bounds[p]
        if mmin > 0:
            cnf = CardEnc.atleast(ys, bound=mmin, top_id=top_id, encoding=EncType.totalizer)
            top_id = max(top_id, cnf.nv)
            clauses.extend(cnf.clauses)
        if mmax < len(ys):
            cnf = CardEnc.atmost(ys, bound=mmax, top_id=top_id, encoding=EncType.totalizer)
            top_id = max(top_id, cnf.nv)
            clauses.extend(cnf.clauses)

    # Total m_in_exact
    if m_in_exact is not None:
        cnf = CardEnc.equals(all_y, bound=m_in_exact, top_id=top_id, encoding=EncType.totalizer)
        top_id = max(top_id, cnf.nv)
        clauses.extend(cnf.clauses)

    # No K6 inside specified parts
    for p in require_no_k6_parts:
        if part_sizes[p] >= 6:
            for sub6 in itertools.combinations(parts[p], 6):
                clauses.append([-edge(sub6[a], sub6[b]) for a in range(6) for b in range(a+1, 6)])

    # Budget constraint: sum(cross_edges) + sum(u_weights[v]*u_var[v]) + (has_u if has_ab_bonus) <= budget
    cross_lits = [x[(u, v)] for u in range(n) for v in range(u+1, n) if v_part[u] != v_part[v]]
    budget_lits = list(cross_lits)
    for v in range(n):
        for _ in range(u_weights[v]):
            budget_lits.append(u_var[v])
    if has_ab_bonus:
        budget_lits.append(has_u)

    cnf_b = CardEnc.atmost(budget_lits, bound=budget, top_id=top_id, encoding=EncType.totalizer)
    top_id = max(top_id, cnf_b.nv)
    clauses.extend(cnf_b.clauses)

    # Turan bound if has_u == 0: e_in + e_out >= t_no_u_bound
    if use_turan_no_u and m_in_exact is not None:
        e_in = sum(sz * (sz - 1) // 2 for sz in part_sizes) - m_in_exact
        need_eout = t_no_u_bound - e_in
        if need_eout > 0:
            cnf_t = CardEnc.atleast(cross_lits, bound=need_eout, top_id=top_id, encoding=EncType.totalizer)
            top_id = max(top_id, cnf_t.nv)
            for cl in cnf_t.clauses:
                clauses.append([has_u] + cl)

    # Generalized Property (L) for parts with fixed m_max (sound upper bound: d(v, V_i) <= (a_i - 5) + (m_max_i - 5*e_min(a_i)))
    for i in range(P):
        if part_sizes[i] < 6:
            continue
        s_max_i = m_bounds[i][1] - 5 * e_min(part_sizes[i])
        d_lim = (part_sizes[i] - 5) + s_max_i
        if d_lim < part_sizes[i]:
            for j in range(P):
                if i == j: continue
                for v in parts[j]:
                    lits = [edge(v, u) for u in parts[i]]
                    cnf_l = CardEnc.atmost(lits, bound=d_lim, top_id=top_id, encoding=EncType.totalizer)
                    top_id = max(top_id, cnf_l.nv)
                    clauses.extend(cnf_l.clauses)

    # Pairwise Cross-Edge upper bound on E_{ij} <= (a_i - 5)*a_j + s_max_i + m_max_j
    for i in range(P):
        if part_sizes[i] < 6: continue
        s_max_i = m_bounds[i][1] - 5 * e_min(part_sizes[i])
        for j in range(P):
            if i == j: continue
            e_lim = (part_sizes[i] - 5) * part_sizes[j] + s_max_i + m_bounds[j][1]
            if e_lim < part_sizes[i] * part_sizes[j]:
                lits = [edge(u, v) for u in parts[i] for v in parts[j]]
                cnf_p = CardEnc.atmost(lits, bound=e_lim, top_id=top_id, encoding=EncType.totalizer)
                top_id = max(top_id, cnf_p.nv)
                clauses.extend(cnf_p.clauses)

    # Solve with incremental CaDiCaL 1.9.5 CEGAR!
    solver = Cadical195(bootstrap_with=clauses)
    iters = 0
    total_cuts = 0
    status = "TIMEOUT"
    witness = None

    while time.time() - t0 < time_limit:
        iters += 1
        sat = solver.solve()
        if not sat:
            status = "UNSAT"
            break
        model = set(solver.get_model())
        adj = [0] * n
        for (u, v), var in x.items():
            if var in model:
                adj[u] |= (1 << v)
                adj[v] |= (1 << u)
        u_val = [1 if u_var[v] in model else 0 for v in range(n)]

        viol = find_violated_is_k(adj, u_val, n, k_is, max_found=80)
        if not viol:
            status = "SAT"
            eo = sum(1 for l in cross_lits if l in model)
            su = sum(u_val)
            m_act = [sum(1 for l in part_y[p] if l in model) for p in range(P)]
            phi = eo + sum(u_weights[v] * u_val[v] for v in range(n)) + (1 if (has_ab_bonus and su > 0) else 0)
            witness = {"e_out": eo, "u_count": su, "phi": phi, "m": m_act}
            break

        for I in viol:
            elits = [edge(I[a], I[b]) for a in range(k_is) for b in range(a+1, k_is)]
            for v in I:
                if u_val[v] == 0:
                    solver.add_clause(elits + [u_var[v]])
                    total_cuts += 1

    dt = time.time() - t0
    solver.delete()
    res = {
        "case": case_id, "status": status, "elapsed_s": round(dt, 2),
        "iters": iters, "cuts": total_cuts, "budget": budget, "witness": witness
    }
    print(json.dumps(res), flush=True)
    return res

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--time-limit", type=float, default=300.0)
    args = ap.parse_args()
    c = args.case
    tl = args.time_limit

    if c == "control_sat":
        # Positive control: relaxed budget 60 on #7 2K6 m_in=12 MUST be SAT!
        res = solve_reduced(c, [8,6,6,5], [(10,10),(1,1),(1,1),(0,0)], [2]*25, 5, 60,
                            require_no_k6_parts=(0,), has_ab_bonus=True, m_in_exact=12, time_limit=60.0)
        assert res["status"] == "SAT", "Positive control failed!"
    elif c == "p6_6B":
        # #6 (7,7,7,6,5,5) Case 6B: V4=pure K6, V1=C1(pure K6)+{v0}. W=(1,7,7,5,5), m=(0,5,5,0,0), budget=28!
        # v0 has u_weight=1 (already has internal edge to C1); others have u_weight=2.
        res = solve_reduced(c, [1,7,7,5,5], [(0,0),(5,5),(5,5),(0,0),(0,0)], [1]+[2]*24, 5, 28,
                            require_no_k6_parts=(1,2), has_ab_bonus=True, m_in_exact=10, time_limit=tl,
                            use_turan_no_u=True, t_no_u_bound=66)
    elif c.startswith("p7_7D_m"):
        mi = int(c.split("_m")[1])
        # #7 (8,6,6,6,6,5) 2K6: W=(8,6,6,5), imbal=2, budget=13+mi, m1>=10, m4>=1, m5>=1, no K6 in V1
        slack = mi - 12
        res = solve_reduced(c, [8,6,6,5], [(10,10+slack),(1,1+slack),(1,1+slack),(0,slack)], [2]*25, 5, 13+mi,
                            require_no_k6_parts=(0,), has_ab_bonus=True, m_in_exact=mi, time_limit=tl)
    elif c == "p7_7B_11":
        # #7 Case 7B: m=(11,1,1,1,1,0), V1 has K6 C1 => delete C1! W1=(2,6,6,6,6,5) (31 verts), u_weights=[0,0]+[1]*29
        # Wait: inside V1, u0,u1 have <=1 edge to C1 (internal), and m1=11 means u0,u1 have 11 non-edges total inside V1,
        # which is at least 10 to C1 and 0 or 1 between u0,u1! So m({u0,u1}) in {0, 1}.
        res = solve_reduced(c, [2,6,6,6,6,5], [(0,1),(1,1),(1,1),(1,1),(1,1),(0,0)], [0,0]+[1]*29, 6, 28,
                            require_no_k6_parts=(), has_ab_bonus=False, m_in_exact=None, time_limit=tl,
                            use_turan_no_u=False)
    elif c == "p7_7B_10":
        # #7 Case 7B: m=(10,2,1,1,1,0), V1 has K6 C1 => W1=(2,6,6,6,6,5)
        res = solve_reduced(c, [2,6,6,6,6,5], [(0,1),(2,2),(1,1),(1,1),(1,1),(0,0)], [0,0]+[1]*29, 6, 28,
                            require_no_k6_parts=(), has_ab_bonus=False, m_in_exact=None, time_limit=tl,
                            use_turan_no_u=False)
    elif c.startswith("p8_8D_m"):
        mi = int(c.split("_m")[1])
        # #8 (7,7,6,6,6,5) 2K6: W=(7,7,6,5), imbal=1, budget=14+mi, m1>=5, m2>=5, m5>=1, no K6 in V1,V2
        slack = mi - 11
        res = solve_reduced(c, [7,7,6,5], [(5,5+slack),(5,5+slack),(1,1+slack),(0,slack)], [2]*25, 5, 14+mi,
                            require_no_k6_parts=(0,1), has_ab_bonus=True, m_in_exact=mi, time_limit=tl)
    elif c.startswith("p9_9D_m"):
        mi = int(c.split("_m")[1])
        # #9 (7,6,6,6,6,6) 2K6: W=(7,6,6,6), imbal=0, budget=15+mi, m1>=5, m4,m5,m6>=1, no K6 in V1
        slack = mi - 8
        res = solve_reduced(c, [7,6,6,6], [(5,5+slack),(1,1+slack),(1,1+slack),(1,1+slack)], [2]*25, 5, 15+mi,
                            require_no_k6_parts=(0,), has_ab_bonus=True, m_in_exact=mi, time_limit=tl)
    else:
        raise ValueError(f"Unknown case {c}")

if __name__ == "__main__":
    main()
