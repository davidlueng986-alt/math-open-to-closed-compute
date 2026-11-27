import argparse
import ctypes
import json
import os
import sys
import time
from itertools import combinations
from pysat.card import CardEnc, EncType, ITotalizer
from pysat.solvers import Cadical195

def e_min(N, r=6):
    q, rem = divmod(N, r)
    return rem * (q + 1) * q // 2 + (r - rem) * q * (q - 1) // 2

def load_oracle():
    lib_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "libfind_is7.so")
    lib = ctypes.CDLL(lib_path)
    lib.find_is7.argtypes = [
        ctypes.POINTER(ctypes.c_uint64),
        ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
        ctypes.c_uint32,
        ctypes.POINTER(ctypes.c_int),
        ctypes.c_int,
    ]
    lib.find_is7.restype = ctypes.c_int
    return lib

def self_test_oracle(lib):
    # Test 1: K_7 union 5 K_6 has alpha == 6 => must return 0
    n = 37
    adj = (ctypes.c_uint64 * n)()
    parts = [range(0, 7), range(7, 13), range(13, 19), range(19, 25), range(25, 31), range(31, 37)]
    for p in parts:
        for u in p:
            for v in p:
                if u != v:
                    adj[u] |= (1 << v)
    out = (ctypes.c_int * (100 * 7))()
    c1 = lib.find_is7(adj, n, 10, 10, 5, 1, out, 100)
    assert c1 == 0, f"Self-test 1 failed: expected 0, got {c1}"
    # Test 2: Remove edge (0, 1) from K_7 => alpha == 7 => must find 7-IS
    adj[0] &= ~(1 << 1)
    adj[1] &= ~(1 << 0)
    c2 = lib.find_is7(adj, n, 10, 10, 5, 1, out, 100)
    assert c2 >= 1, f"Self-test 2 failed: expected >=1, got {c2}"
    # Verify returned set is truly independent
    s = [out[i] for i in range(7)]
    for i in range(7):
        for j in range(i + 1, 7):
            assert not ((adj[s[i]] >> s[j]) & 1), f"Returned set {s} is not independent!"
    print("Oracle self-test PASSED (K_7 + 5K_6 -> 0; minus 1 edge -> valid 7-IS).", flush=True)

def solve_ordering(a, lib, max_time=1200.0):
    t0 = time.time()
    n = sum(a)
    assert n == 37
    parts = []
    cur = 0
    for sz in a:
        parts.append(list(range(cur, cur + sz)))
        cur += sz

    # Variable numbering: 1..666 for edges (u, v) with u < v
    edge_var = {}
    vid = 1
    for u in range(n):
        for v in range(u + 1, n):
            edge_var[(u, v)] = vid
            vid += 1
    top_id = vid - 1

    def getx(u, v):
        return edge_var[(u, v)] if u < v else edge_var[(v, u)]

    solver = Cadical195()

    def add_atmost(lits, bound):
        nonlocal top_id
        if bound < 0:
            solver.add_clause([])
            return
        if bound >= len(lits):
            return
        cnf = CardEnc.atmost(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
        top_id = max(top_id, cnf.nv)
        for cl in cnf.clauses:
            solver.add_clause(cl)

    def add_atleast(lits, bound):
        nonlocal top_id
        if bound <= 0:
            return
        if bound > len(lits):
            solver.add_clause([])
            return
        cnf = CardEnc.atleast(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
        top_id = max(top_id, cnf.nv)
        for cl in cnf.clauses:
            solver.add_clause(cl)

    # 1. Greedy peeling fixed edges:
    # - v_i = parts[i][0] adjacent to all other vertices in V_i
    # - v_i has NO edges to V_j for j > i
    # - Last part V_5 is a clique (m_5 = 0)
    for i in range(6):
        vi = parts[i][0]
        for u in parts[i][1:]:
            solver.add_clause([getx(vi, u)])
        for j in range(i + 1, 6):
            for u in parts[j]:
                solver.add_clause([-getx(vi, u)])
    for idx1 in range(len(parts[5])):
        for idx2 in range(idx1 + 1, len(parts[5])):
            solver.add_clause([getx(parts[5][idx1], parts[5][idx2])])

    # 2. Pointwise greedy peeling degree condition:
    # For every i and every w in U_i, deg_{G_1[U_i]}(w) >= a[i] - 1
    for i in range(6):
        Ui_verts = [v for k in range(i, 6) for v in parts[k]]
        for k in range(i, 6):
            start_idx = 1 if k == i else 0
            for w in parts[k][start_idx:]:
                lits = [getx(w, u) for u in Ui_verts if u != w]
                add_atleast(lits, a[i] - 1)

    # 3. Total edges <= 111
    all_edge_lits = list(edge_var.values())
    add_atmost(all_edge_lits, 111)

    # 4. Exact Turan subset bounds for ALL T of size 1..6:
    # e(G_1[U_T]) <= C(N_T, 2) - 5 * e_min(N_T, 6)
    for k in range(1, 7):
        for T in combinations(range(6), k):
            verts_T = [v for i in T for v in parts[i]]
            N_T = len(verts_T)
            max_edges_T = N_T * (N_T - 1) // 2 - 5 * e_min(N_T, 6)
            lits_T = [getx(verts_T[p], verts_T[q]) for p in range(N_T) for q in range(p + 1, N_T)]
            add_atmost(lits_T, max_edges_T)

    # Precompute internal edge literals (inside V_i \ {v_i}) and m_ge_1 / m_ge_2 indicators
    in_edges = []
    miss_edges = []
    m_ge_1 = []
    m_ge_2 = []
    for i in range(6):
        ie = [getx(parts[i][u], parts[i][v]) for u in range(1, a[i]) for v in range(u + 1, a[i])]
        me = [-l for l in ie]
        in_edges.append(ie)
        miss_edges.append(me)
        if i == 5:
            # m_5 == 0
            m_ge_1.append(None)
            m_ge_2.append(None)
        else:
            tot_m = ITotalizer(lits=me, ubound=2, top_id=top_id)
            top_id = max(top_id, tot_m.top_id)
            for cl in tot_m.cnf.clauses:
                solver.add_clause(cl)
            g1, g2 = tot_m.rhs[0], tot_m.rhs[1]
            # Reverse implications so m==0 => -g1 and m<=1 => -g2!
            solver.add_clause([-g1] + me)
            for idx_skip in range(len(me)):
                solver.add_clause([-g2] + [me[j] for j in range(len(me)) if j != idx_skip])
            m_ge_1.append(g1)
            m_ge_2.append(g2)

    # 5. Pairwise Cross-Edge Theorem!
    for dst in range(6):
        if a[dst] == 6:
            for src in range(6):
                if src == dst:
                    continue
                B = parts[src][1:] if src < dst else parts[src]
                excess_lits = []
                deg_ge2 = {}
                for u in B:
                    lits_u = [getx(u, w) for w in parts[dst]]
                    tot_u = ITotalizer(lits=lits_u, ubound=6, top_id=top_id)
                    top_id = max(top_id, tot_u.top_id)
                    for cl in tot_u.cnf.clauses:
                        solver.add_clause(cl)
                    # tot_u.rhs[1..5] represent d(u, V_dst) >= 2..6
                    deg_ge2[u] = tot_u.rhs[1]
                    excess_lits.extend(tot_u.rhs[1:])
                    # If m[dst] == 0: d(u, V_dst) <= 1 => -deg_ge2[u]
                    if m_ge_1[dst] is None:
                        solver.add_clause([-deg_ge2[u]])
                    else:
                        solver.add_clause([m_ge_1[dst], -deg_ge2[u]])

                # If m[dst] <= 1: H_2(V_dst) is a G_1-independent set!
                if m_ge_2[dst] is not None:
                    for idx1 in range(len(B)):
                        for idx2 in range(idx1 + 1, len(B)):
                            u1, u2 = B[idx1], B[idx2]
                            solver.add_clause([m_ge_2[dst], -deg_ge2[u1], -deg_ge2[u2], -getx(u1, u2)])

                # General Pairwise Cross-Edge: sum_{u in B} max(0, d(u, V_dst) - 1) <= m[dst] + m[src]
                # <=> sum(excess_lits) + sum(in_edges[dst]) + sum(in_edges[src]) <= |in_edges[dst]| + |in_edges[src]|
                bound_pce = len(in_edges[dst]) + len(in_edges[src])
                add_atmost(excess_lits + in_edges[dst] + in_edges[src], bound_pce)

        elif a[dst] == 5:
            for src in range(6):
                if src == dst:
                    continue
                B = parts[src][1:] if src < dst else parts[src]
                cross_lits = [getx(u, w) for u in B for w in parts[dst]]
                bound_pce5 = 5 + len(in_edges[dst]) + len(in_edges[src])
                add_atmost(cross_lits + in_edges[dst] + in_edges[src], bound_pce5)

    # 6. Sound Symmetry Breaking: within each V_i \ {v_i}, sort by total degree in G_1 descending!
    # Encode via ITotalizer on total degree (ubound=12? No, max deg in G_1 could be up to 36, but sorting by
    # internal missing degree deg_{F_i}(u) descending is tiny (ubound = a[i]-2 <= 5) and 100% sound!).
    for i in range(6):
        if a[i] <= 2 or i == 5:
            continue
        sub = parts[i][1:]
        sub_tots = []
        ub = len(sub) - 1
        for u in sub:
            ml = [-getx(u, v) for v in sub if v != u]
            tot = ITotalizer(lits=ml, ubound=ub, top_id=top_id)
            top_id = max(top_id, tot.top_id)
            for cl in tot.cnf.clauses:
                solver.add_clause(cl)
            # Make exact (need reverse too? Actually, for sym-breaking, if we just want deg(u_0) >= deg(u_1) >= ...,
            # wait: one-sided rhs[k] doesn't force rhs[k] false when deg < k. So add reverse ONLY for small ub,
            # OR use CardEnc? Wait: without reverse, rhs[k] could be set true freely, which makes sym-breaking vacuous
            # (still 100% sound!). To make it active, we skip sym-breaking or only sort on a[i]==7?
            # Actually, CaDiCaL doesn't even need sym-breaking — let's keep it clean and 100% sound without extra vars!)
            pass

    print(f"Encoded ordering a={a}: vars={top_id}, setup={time.time()-t0:.2f}s", flush=True)

    # 7. Incremental CEGAR loop!
    out_buf = (ctypes.c_int * (120 * 7))()
    total_cuts = 0
    it = 0
    while True:
        elapsed = time.time() - t0
        if elapsed > max_time:
            print(f"TIMEOUT ordering a={a}: iters={it}, cuts={total_cuts}, time={elapsed:.1f}s", flush=True)
            return {"ordering": list(a), "status": "TIMEOUT", "iters": it, "cuts": total_cuts, "time": elapsed}

        it += 1
        sat = solver.solve()
        if not sat:
            elapsed = time.time() - t0
            print(f">>> UNSAT ordering a={a}: iters={it}, cuts={total_cuts}, time={elapsed:.2f}s <<<", flush=True)
            return {"ordering": list(a), "status": "UNSAT", "iters": it, "cuts": total_cuts, "time": elapsed}

        model = solver.get_model()
        adj = (ctypes.c_uint64 * n)()
        edge_count = 0
        for (u, v), vid_uv in edge_var.items():
            if model[vid_uv - 1] > 0:
                adj[u] |= (1 << v)
                adj[v] |= (1 << u)
                edge_count += 1

        n_is = lib.find_is7(adj, n, 15, 25, 5, it, out_buf, 100)
        if n_is == 0:
            elapsed = time.time() - t0
            mv = [sum(1 for l in miss_edges[i] if model[abs(l) - 1] < 0) for i in range(6)]
            print(f">>> SAT (VALID G_1 FOUND!) ordering a={a}: iters={it}, edges={edge_count}, m={mv}, time={elapsed:.2f}s <<<", flush=True)
            edges_list = [[u, v] for (u, v), vid_uv in edge_var.items() if model[vid_uv - 1] > 0]
            return {"ordering": list(a), "status": "SAT", "iters": it, "cuts": total_cuts, "time": elapsed,
                    "edges_count": edge_count, "m": mv, "edges": edges_list}

        for idx in range(n_is):
            S = [out_buf[idx * 7 + k] for k in range(7)]
            cl = [getx(S[p], S[q]) for p in range(7) for q in range(p + 1, 7)]
            solver.add_clause(cl)
        total_cuts += n_is
        if it <= 5 or it % 50 == 0:
            mv = [sum(1 for l in miss_edges[i] if model[abs(l) - 1] < 0) for i in range(6)]
            print(f"  iter={it:4d} cuts={total_cuts:6d} edges={edge_count} m={mv} t={time.time()-t0:.1f}s", flush=True)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ordering", type=str, required=True, help="Comma-separated 6 ints, e.g. 6,7,6,6,6,6")
    parser.add_argument("--max-time", type=float, default=1200.0)
    parser.add_argument("--out", type=str, default="result.json")
    args = parser.parse_args()

    a = tuple(int(x) for x in args.ordering.split(","))
    lib = load_oracle()
    self_test_oracle(lib)
    res = solve_ordering(a, lib, max_time=args.max_time)
    with open(args.out, "w") as f:
        json.dump(res, f, indent=2)
    print("Wrote", args.out, flush=True)

if __name__ == "__main__":
    main()
