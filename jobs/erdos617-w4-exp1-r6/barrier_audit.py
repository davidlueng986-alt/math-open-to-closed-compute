import argparse, itertools, json, time
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType

def e_min(N, r=6):
    q, rem = divmod(N, r)
    return rem * (q + 1) * q // 2 + (r - rem) * q * (q - 1) // 2

def find_independent_sets(n, adj, k, limit=300):
    res = []
    full = (1 << n) - 1
    def bt(cur, cand, rem):
        if len(res) >= limit: return
        if rem == 0:
            res.append(cur)
            return
        if cand.bit_count() < rem: return
        while cand:
            lsb = cand & -cand
            v = lsb.bit_length() - 1
            cand ^= lsb
            bt(cur + (v,), cand & ~adj[v], rem - 1)
    bt((), full, k)
    return res

def find_cliques(n, adj, k, limit=100):
    res = []
    full = (1 << n) - 1
    def bt(cur, cand, rem):
        if len(res) >= limit: return
        if rem == 0:
            res.append(cur)
            return
        if cand.bit_count() < rem: return
        while cand:
            lsb = cand & -cand
            v = lsb.bit_length() - 1
            cand ^= lsb
            bt(cur + (v,), cand & adj[v], rem - 1)
    bt((), full, k)
    return res

def verify_all_wave3_g1_conditions(w_sizes, m_vals, internal_non_edges, cross_edges):
    """
    Independently verify ALL Wave 1-3 G1-only theorems on the 37-vertex graph
    G1 = K6(A) + K6(B) + G1[W] (with e(A, W) = e(B, W) = e(A, B) = 0).
    """
    n_w = sum(w_sizes)
    assert n_w == 25
    part_of = []
    part_nodes = []
    cur = 0
    for p, sz in enumerate(w_sizes):
        part_nodes.append(list(range(cur, cur + sz)))
        part_of.extend([p] * sz)
        cur += sz

    adj = [0] * n_w
    edges_w = set()
    # Internal edges
    for p, sz in enumerate(w_sizes):
        nodes = part_nodes[p]
        for i in range(sz):
            for j in range(i + 1, sz):
                u, v = nodes[i], nodes[j]
                if (u, v) not in internal_non_edges:
                    adj[u] |= (1 << v); adj[v] |= (1 << u)
                    edges_w.add((u, v))
    for u, v in cross_edges:
        adj[u] |= (1 << v); adj[v] |= (1 << u)
        edges_w.add((min(u, v), max(u, v)))

    # 1. Total edges in G1 = 30 + |edges_w| <= 111
    total_e = 30 + len(edges_w)
    # 2. alpha(W) <= 4 => alpha(G1) <= 6
    is5 = find_independent_sets(n_w, adj, 5, limit=1)
    # 3. No K6 in W => strictly at most 2 disjoint K6 in G1 (in fact, only A and B!)
    k6s = find_cliques(n_w, adj, 6, limit=1)
    # 4. Degrees: delta(G1) >= 4, Delta(G1) >= 7
    degs = [adj[u].bit_count() for u in range(n_w)] + [5]*12
    min_deg = min(degs)
    max_deg = max(degs)
    # 5. Generalized Property (L) & Pairwise Cross-Edge Theorem for all pairs in W
    prop_l_ok = True
    pce_ok = True
    for i in range(4):
        if w_sizes[i] < 6: continue
        k_i = w_sizes[i] - 6
        s_i = m_vals[i] - 5 * e_min(w_sizes[i], 6)
        mask_i = 0
        for u in part_nodes[i]: mask_i |= (1 << u)
        for j in range(4):
            if j == i: continue
            excess = 0
            for x in part_nodes[j]:
                d = (adj[x] & mask_i).bit_count()
                if d > k_i + 1 + s_i:
                    prop_l_ok = False
                if d > k_i + 1:
                    excess += d - (k_i + 1)
            if excess > s_i + m_vals[j]:
                pce_ok = False
    # 6. Exact Turan Subset Cross-Edge Bound for all non-empty subsets T of W (and with A, B!)
    # Full 6-part sizes: w_sizes + [6, 6], m_full = m_vals + [0, 0]
    full_sizes = list(w_sizes) + [6, 6]
    full_m = list(m_vals) + [0, 0]
    E_mat = [[0]*6 for _ in range(6)]
    for u, v in cross_edges:
        pi, pj = part_of[u], part_of[v]
        E_mat[pi][pj] += 1
        E_mat[pj][pi] += 1
    turan_ok = True
    for mask in range(1, 64):
        T = [i for i in range(6) if (mask >> i) & 1]
        if len(T) < 2: continue
        N_T = sum(full_sizes[i] for i in T)
        lhs = sum(E_mat[T[a]][T[b]] for a in range(len(T)) for b in range(a+1, len(T)))
        rhs = sum(full_sizes[T[a]]*full_sizes[T[b]] for a in range(len(T)) for b in range(a+1, len(T))) - 5*e_min(N_T, 6) + sum(full_m[i] for i in T)
        if lhs > rhs:
            turan_ok = False
            break

    return {
        "total_edges_G1": total_e,
        "alpha_W_le_4": len(is5) == 0,
        "no_K6_in_W": len(k6s) == 0,
        "min_deg": min_deg,
        "max_deg": max_deg,
        "prop_l_ok": prop_l_ok,
        "pairwise_cross_edge_ok": pce_ok,
        "turan_subset_ok": turan_ok,
        "ALL_WAVE3_G1_PASS": (
            total_e <= 111 and len(is5) == 0 and len(k6s) == 0
            and min_deg >= 4 and max_deg >= 7
            and prop_l_ok and pce_ok and turan_ok
        )
    }

def solve_strict_barrier(name, w_sizes, m_vals, max_eout, time_limit=300):
    t0 = time.time()
    n = sum(w_sizes)
    part_of = []
    part_nodes = []
    cur = 0
    for p, sz in enumerate(w_sizes):
        part_nodes.append(list(range(cur, cur + sz)))
        part_of.extend([p] * sz)
        cur += sz

    # Variables:
    # For internal pairs (u,v) in part p: h[(u,v)] = 1 means NON-EDGE in G1 (edge in H_p)
    # For cross pairs (u,v): x[(u,v)] = 1 means EDGE in G1
    vpool = 0
    def new_var():
        nonlocal vpool
        vpool += 1
        return vpool

    h = {}
    part_int_vars = [[] for _ in range(4)]
    for p, sz in enumerate(w_sizes):
        nodes = part_nodes[p]
        for i in range(sz):
            for j in range(i + 1, sz):
                var = new_var()
                h[(nodes[i], nodes[j])] = var
                part_int_vars[p].append(var)

    x = {}
    cross_vars = []
    for u in range(n):
        for v in range(u + 1, n):
            if part_of[u] != part_of[v]:
                var = new_var()
                x[(u, v)] = var
                cross_vars.append(var)

    solver = Cadical195()

    # Exact m_p counts for each part
    for p in range(4):
        if m_vals[p] == 0:
            for var in part_int_vars[p]:
                solver.add_clause([-var])
        else:
            cnf = CardEnc.equals(lits=part_int_vars[p], bound=m_vals[p], top_id=vpool, encoding=EncType.totalizer)
            vpool = max(vpool, cnf.nv)
            for cl in cnf.clauses: solver.add_clause(cl)

    # e_out <= max_eout
    cnf = CardEnc.atmost(lits=cross_vars, bound=max_eout, top_id=vpool, encoding=EncType.totalizer)
    vpool = max(vpool, cnf.nv)
    for cl in cnf.clauses: solver.add_clause(cl)

    # delta(G1) >= 4 for every vertex u in W:
    # deg(u) = (sz_p - 1 - sum h_int(u)) + sum x_cross(u) >= 4
    # <=> sum h_int(u) + sum (~x_cross(u)) <= (n - 1) - 4 ... better:
    # deg(u) >= 4 <=> sum (~h_int(u)) + sum x_cross(u) >= 4
    for u in range(n):
        p = part_of[u]
        lits = []
        for v in part_nodes[p]:
            if v != u:
                lits.append(-h[(min(u, v), max(u, v))])
        for v in range(n):
            if part_of[v] != p:
                lits.append(x[(min(u, v), max(u, v))])
        cnf = CardEnc.atleast(lits=lits, bound=4, top_id=vpool, encoding=EncType.totalizer)
        vpool = max(vpool, cnf.nv)
        for cl in cnf.clauses: solver.add_clause(cl)

    # Generalized Property (L) for parts of size >= 6:
    # d(u, V_i) <= k_i + 1 + s_i
    for i in range(4):
        if w_sizes[i] < 6: continue
        k_i = w_sizes[i] - 6
        s_i = m_vals[i] - 5 * e_min(w_sizes[i], 6)
        lim = k_i + 1 + s_i
        for u in range(n):
            if part_of[u] == i: continue
            lits = [x[(min(u, v), max(u, v))] for v in part_nodes[i]]
            if lim < len(lits):
                cnf = CardEnc.atmost(lits=lits, bound=lim, top_id=vpool, encoding=EncType.totalizer)
                vpool = max(vpool, cnf.nv)
                for cl in cnf.clauses: solver.add_clause(cl)

    # Pairwise Cross-Edge Theorem: for each ordered pair (i, j) with w_sizes[i] >= 6,
    # sum_{u in V_j} max(0, d(u, V_i) - (k_i + 1)) <= s_i + m_j.
    # For simplicity, also enforce the weaker necessary condition: e(V_i, V_j) <= |V_j|*(k_i+1) + s_i + m_j,
    # and check exact PCE in CEGAR if ever violated!
    # Also forbid K6 inside each part V_p of size >= 6 directly (every 6-subset of V_p has >= 1 non-edge h)!
    for p in range(4):
        if w_sizes[p] >= 6:
            for sub in itertools.combinations(part_nodes[p], 6):
                solver.add_clause([h[(u, v)] for u, v in itertools.combinations(sub, 2)])

    # Exact Turan Subset Bound for 2-part and 3-part subsets of W:
    for r_sub in [2, 3]:
        for T in itertools.combinations(range(4), r_sub):
            N_T = sum(w_sizes[i] for i in T)
            rhs = sum(w_sizes[T[a]]*w_sizes[T[b]] for a in range(r_sub) for b in range(a+1, r_sub)) - 5*e_min(N_T, 6) + sum(m_vals[i] for i in T)
            lits = []
            for a in range(r_sub):
                for b in range(a+1, r_sub):
                    for u in part_nodes[T[a]]:
                        for v in part_nodes[T[b]]:
                            lits.append(x[(min(u, v), max(u, v))])
            if rhs < len(lits):
                cnf = CardEnc.atmost(lits=lits, bound=rhs, top_id=vpool, encoding=EncType.totalizer)
                vpool = max(vpool, cnf.nv)
                for cl in cnf.clauses: solver.add_clause(cl)

    iters = 0
    cuts = 0
    while time.time() - t0 < time_limit:
        iters += 1
        sat = solver.solve()
        if not sat:
            print(json.dumps({"case": name, "status": "UNSAT", "elapsed_s": round(time.time()-t0, 2), "iters": iters, "cuts": cuts}))
            return
        model = set(solver.get_model())
        adj = [0] * n
        int_non = set()
        cross_on = []
        for (u, v), var in h.items():
            if var in model:
                int_non.add((u, v))
            else:
                adj[u] |= (1 << v); adj[v] |= (1 << u)
        for (u, v), var in x.items():
            if var in model:
                adj[u] |= (1 << v); adj[v] |= (1 << u)
                cross_on.append((u, v))

        is5 = find_independent_sets(n, adj, 5, limit=300)
        k6s = find_cliques(n, adj, 6, limit=100)
        # Check exact PCE violation
        pce_cuts = []
        for i in range(4):
            if w_sizes[i] < 6: continue
            k_i = w_sizes[i] - 6
            s_i = m_vals[i] - 5 * e_min(w_sizes[i], 6)
            mask_i = 0
            for u in part_nodes[i]: mask_i |= (1 << u)
            for j in range(4):
                if j == i: continue
                excess_edges = []
                excess_val = 0
                for u in part_nodes[j]:
                    nbrs = [v for v in part_nodes[i] if (adj[u] >> v) & 1]
                    if len(nbrs) > k_i + 1:
                        excess_val += len(nbrs) - (k_i + 1)
                        for v in nbrs:
                            excess_edges.append(x[(min(u, v), max(u, v))])
                if excess_val > s_i + m_vals[j]:
                    pce_cuts.append([-var for var in excess_edges])

        if not is5 and not k6s and not pce_cuts:
            audit = verify_all_wave3_g1_conditions(w_sizes, m_vals, int_non, cross_on)
            if audit["ALL_WAVE3_G1_PASS"]:
                print(json.dumps({
                    "case": name,
                    "status": "SAT_STRICT_BARRIER",
                    "elapsed_s": round(time.time()-t0, 2),
                    "iters": iters,
                    "cuts": cuts,
                    "w_sizes": w_sizes,
                    "m_vals": m_vals,
                    "e_out": len(cross_on),
                    "audit": audit,
                    "internal_non_edges": sorted(list(int_non)),
                    "cross_edges": sorted(cross_on)
                }))
                return
            else:
                # Block this exact cross_on if Delta < 7 (rare)
                solver.add_clause([-x[e] for e in cross_on])
                cuts += 1
                continue

        for s in is5:
            cl = []
            for u, v in itertools.combinations(s, 2):
                if part_of[u] == part_of[v]:
                    cl.append(-h[(min(u, v), max(u, v))])
                else:
                    cl.append(x[(min(u, v), max(u, v))])
            solver.add_clause(cl)
            cuts += 1
        for c in k6s:
            cl = []
            for u, v in itertools.combinations(c, 2):
                if part_of[u] == part_of[v]:
                    cl.append(h[(min(u, v), max(u, v))])
                else:
                    cl.append(-x[(min(u, v), max(u, v))])
            solver.add_clause(cl)
            cuts += 1
        for cl in pce_cuts:
            solver.add_clause(cl)
            cuts += 1

    print(json.dumps({"case": name, "status": "TIMEOUT", "elapsed_s": round(time.time()-t0, 2), "iters": iters, "cuts": cuts}))

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--time-limit", type=int, default=300)
    args = ap.parse_args()
    CASES = {
        "p7_barrier": ([8, 6, 6, 5], [10, 4, 1, 0], 28),
        "p7_barrier_m14": ([8, 6, 6, 5], [12, 1, 1, 0], 27),
        "p8_barrier": ([7, 7, 6, 5], [5, 5, 5, 0], 29),
        "p8_barrier_m14": ([7, 7, 6, 5], [6, 7, 1, 0], 28),
        "p9_barrier": ([7, 6, 6, 6], [10, 1, 2, 1], 29),
        "p9_barrier_m15": ([7, 6, 6, 6], [9, 2, 2, 2], 30),
    }
    w_sizes, m_vals, max_eout = CASES[args.case]
    solve_strict_barrier(args.case, w_sizes, m_vals, max_eout, args.time_limit)
