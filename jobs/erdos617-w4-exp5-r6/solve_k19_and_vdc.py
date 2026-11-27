import argparse, ctypes, json, os, sys, time
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def e_min(N, r=6):
    if N <= r or r <= 0:
        return 0
    q, rem = divmod(N, r)
    return rem * (q + 1) * q // 2 + (r - rem) * q * (q - 1) // 2

def load_oracle():
    lib_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "libfind_is7.so")
    lib = ctypes.CDLL(lib_path)
    lib.find_is7.argtypes = [
        ctypes.POINTER(ctypes.c_uint64), ctypes.c_int, ctypes.c_int,
        ctypes.POINTER(ctypes.c_int), ctypes.c_int
    ]
    lib.find_is7.restype = ctypes.c_int
    return lib

def find_is_k_py(adj, n, k, max_found=50):
    found = []
    non_nbr = [0] * n
    full = (1 << n) - 1
    for v in range(n):
        non_nbr[v] = (full ^ ((1 << (v + 1)) - 1)) & ~adj[v]
    def dfs(cand, chosen, need):
        if len(found) >= max_found:
            return
        if need == 0:
            found.append(tuple(chosen))
            return
        if cand.bit_count() < need:
            return
        c = cand
        while c:
            lsb = c & -c
            v = lsb.bit_length() - 1
            c ^= lsb
            if (c.bit_count() + 1) < need:
                break
            chosen.append(v)
            dfs(c & non_nbr[v], chosen, need - 1)
            chosen.pop()
            if len(found) >= max_found:
                return
    dfs(full, [], k)
    return found

def solve_k19_5color(max_time=900.0, out_path="result_k19.json"):
    """Exact CaDiCaL CEGAR: Does K_19 admit a 6-edge-coloring (H_19, G_2..G_6)
    with alpha(H_19) <= 3, delta(H_19) >= 6, e(H_19) <= 66, and alpha(G_c) <= 6 for c=2..6?"""
    t0 = time.time()
    n = 19
    vpool = IDPool()
    solver = Cadical195()
    # y[(c,u,v)] for c in 0..5, 0 <= u < v < 19
    y = {}
    for u in range(n):
        for v in range(u + 1, n):
            lits = [vpool.id(("c", c, u, v)) for c in range(6)]
            # Exactly one color per edge
            solver.add_clause(lits)
            for i in range(6):
                for j in range(i + 1, 6):
                    solver.add_clause([-lits[i], -lits[j]])
            for c in range(6):
                y[(c, u, v)] = lits[c]

    def Y(c, u, v):
        return y[(c, u, v)] if u < v else y[(c, v, u)]

    # Symmetry breaking: vertex 0 has deg_{H_19}(0) = 6 (peeling pivot of a=(7,7,5) or min deg)
    # Wait: keep general delta(H_19) >= 6, only break color symmetry on edges of 0:
    # Actually just break color symmetry on non-H_19 edges incident to 0, or minimal symmetry:
    # Forbid nothing that could lose solutions! Just delta(H_19) >= 6:
    for u in range(n):
        lits = [Y(0, u, v) for v in range(n) if v != u]
        cnf = CardEnc.atleast(lits=lits, bound=6, vpool=vpool, encoding=EncType.kmtotalizer)
        for cl in cnf.clauses:
            solver.add_clause(cl)

    # e(H_19) <= 66
    h_lits = [y[(0, u, v)] for u in range(n) for v in range(u + 1, n)]
    cnf = CardEnc.atmost(lits=h_lits, bound=66, vpool=vpool, encoding=EncType.kmtotalizer)
    for cl in cnf.clauses:
        solver.add_clause(cl)

    # Each G_c (c=1..5) has e(G_c) >= 21 = e_min(19, 6)
    for c in range(1, 6):
        c_lits = [y[(c, u, v)] for u in range(n) for v in range(u + 1, n)]
        cnf = CardEnc.atleast(lits=c_lits, bound=21, vpool=vpool, encoding=EncType.kmtotalizer)
        for cl in cnf.clauses:
            solver.add_clause(cl)

    print(f"Encoded K_19 (H_19 + 5 colors): vars={vpool.top}, setup={time.time()-t0:.2f}s", flush=True)
    cuts = 0
    for it in range(1, 50000):
        if time.time() - t0 > max_time:
            res = {"mode": "k19", "status": "TIMEOUT", "iters": it, "cuts": cuts, "time": time.time() - t0}
            with open(out_path, "w") as f: json.dump(res, f, indent=2)
            print(f"TIMEOUT k19 iters={it} cuts={cuts}", flush=True)
            return
        sat = solver.solve()
        if not sat:
            res = {"mode": "k19", "status": "UNSAT", "iters": it, "cuts": cuts, "time": time.time() - t0}
            with open(out_path, "w") as f: json.dump(res, f, indent=2)
            print(f">>> UNSAT K_19 (H_19 + 5 colors): iters={it}, cuts={cuts}, time={time.time()-t0:.2f}s <<<", flush=True)
            return
        model = set(l for l in solver.get_model() if l > 0)
        new_cuts = 0
        for c in range(6):
            adj = [0] * n
            for u in range(n):
                for v in range(u + 1, n):
                    if y[(c, u, v)] in model:
                        adj[u] |= 1 << v
                        adj[v] |= 1 << u
            k = 4 if c == 0 else 7
            iss = find_is_k_py(adj, n, k, 30)
            for S in iss:
                cl = [Y(c, S[i], S[j]) for i in range(k) for j in range(i + 1, k)]
                solver.add_clause(cl)
            new_cuts += len(iss)
        if new_cuts == 0:
            edges_by_c = {}
            for c in range(6):
                edges_by_c[str(c)] = [[u, v] for u in range(n) for v in range(u + 1, n) if y[(c, u, v)] in model]
            res = {
                "mode": "k19", "status": "SAT", "iters": it, "cuts": cuts,
                "time": time.time() - t0,
                "counts": [len(edges_by_c[str(c)]) for c in range(6)],
                "edges": edges_by_c
            }
            with open(out_path, "w") as f: json.dump(res, f, indent=2)
            print(f">>> SAT!! K_19 (H_19 + 5 colors): counts={res['counts']}, iters={it}, cuts={cuts}, time={time.time()-t0:.2f}s <<<", flush=True)
            return
        cuts += new_cuts
        if it <= 5 or it % 50 == 0:
            print(f"  iter={it:4d} cuts={cuts:6d} new={new_cuts:3d} t={time.time()-t0:.1f}s", flush=True)

def solve_ordering_vdc(a, max_time=1200.0, out_path="result.json"):
    """Incremental CaDiCaL CEGAR with Vertex-Degree Turan Coupling Lemma!"""
    t0 = time.time()
    lib = load_oracle()
    n = 37
    parts, cur = [], 0
    for sz in a:
        parts.append(list(range(cur, cur + sz)))
        cur += sz
    pivots = [p[0] for p in parts]

    vpool = IDPool()
    solver = Cadical195()
    x = {}
    for u in range(n):
        for v in range(u + 1, n):
            x[(u, v)] = vpool.id(("e", u, v))
    def E(u, v):
        return x[(u, v)] if u < v else x[(v, u)]

    # 1. Peeling structure
    for i in range(6):
        p = pivots[i]
        for u in parts[i][1:]:
            solver.add_clause([E(p, u)])
        for j in range(i + 1, 6):
            for u in parts[j]:
                solver.add_clause([-E(p, u)])

    # 2. Minimum-degree peeling condition
    for i in range(6):
        Ui = [u for k in range(i, 6) for u in parts[k]]
        for u in Ui:
            if u == pivots[i]:
                continue
            lits = [E(u, w) for w in Ui if w != u]
            cnf = CardEnc.atleast(lits=lits, bound=a[i] - 1, vpool=vpool, encoding=EncType.kmtotalizer)
            for cl in cnf.clauses:
                solver.add_clause(cl)

    # 3. Total edges <= 111
    all_e = list(x.values())
    cnf = CardEnc.atmost(lits=all_e, bound=111, vpool=vpool, encoding=EncType.kmtotalizer)
    for cl in cnf.clauses:
        solver.add_clause(cl)

    # 4. Exact Turan subset edge bounds + Vertex-Degree Turan Coupling!
    vdc_rhs = {12: 42, 13: 45, 14: 49, 18: 70, 19: 74, 20: 79}
    for mask in range(1, 64):
        T = [i for i in range(6) if (mask >> i) & 1]
        U_T = [u for i in T for u in parts[i]]
        N_T = len(U_T)
        if N_T < 7:
            continue
        edges_T = [E(U_T[p], U_T[q]) for p in range(N_T) for q in range(p + 1, N_T)]
        max_e1 = N_T * (N_T - 1) // 2 - 5 * e_min(N_T, 6)
        if max_e1 < len(edges_T):
            cnf = CardEnc.atmost(lits=edges_T, bound=max_e1, vpool=vpool, encoding=EncType.kmtotalizer)
            for cl in cnf.clauses:
                solver.add_clause(cl)
        # Vertex-Degree Turan Coupling on subsets of size 19 (and 14 if both 7s):
        # e1(U_T) + deg_{U_T}(v) <= vdc_rhs[N_T]
        # Only add on subsets containing ALL parts of size 7 (or N_T == 19) to keep CNF lean!
        has_7 = any(a[i] == 7 for i in T)
        if N_T in vdc_rhs and has_7 and N_T in (14, 19):
            rhs = vdc_rhs[N_T]
            for v in U_T:
                deg_lits = [E(v, w) for w in U_T if w != v]
                # Duplicate deg_lits in edges_T -> sum is e1(U_T) + deg(v)
                comb = edges_T + deg_lits
                cnf = CardEnc.atmost(lits=comb, bound=rhs, vpool=vpool, encoding=EncType.kmtotalizer)
                for cl in cnf.clauses:
                    solver.add_clause(cl)

    print(f"Encoded VDC ordering a={a}: vars={vpool.top}, setup={time.time()-t0:.2f}s", flush=True)
    out_buf = (ctypes.c_int * (100 * 7))()
    adj_arr = (ctypes.c_uint64 * 37)()
    cuts = 0
    for it in range(1, 100000):
        if time.time() - t0 > max_time:
            res = {"ordering": list(a), "status": "TIMEOUT", "iters": it, "cuts": cuts, "time": time.time() - t0}
            with open(out_path, "w") as f: json.dump(res, f, indent=2)
            print(f"TIMEOUT a={a} iters={it} cuts={cuts}", flush=True)
            return
        sat = solver.solve()
        if not sat:
            res = {"ordering": list(a), "status": "UNSAT", "iters": it, "cuts": cuts, "time": time.time() - t0}
            with open(out_path, "w") as f: json.dump(res, f, indent=2)
            print(f">>> UNSAT (VDC) a={a}: iters={it}, cuts={cuts}, time={time.time()-t0:.2f}s <<<", flush=True)
            return
        model = set(l for l in solver.get_model() if l > 0)
        for u in range(n):
            adj_arr[u] = 0
        ec = 0
        edges_list = []
        for (u, v), vid in x.items():
            if vid in model:
                adj_arr[u] |= (1 << v)
                adj_arr[v] |= (1 << u)
                ec += 1
                edges_list.append([u, v])
        found = lib.find_is7(adj_arr, 37, 7, out_buf, 100)
        if found == 0:
            degs = [bin(adj_arr[u]).count('1') for u in range(n)]
            res = {
                "ordering": list(a), "status": "SAT", "iters": it, "cuts": cuts,
                "time": time.time() - t0, "edges_count": ec, "degs": degs, "edges": edges_list
            }
            with open(out_path, "w") as f: json.dump(res, f, indent=2)
            print(f">>> SAT (VDC) a={a}: edges={ec}, iters={it}, cuts={cuts}, time={time.time()-t0:.2f}s <<<", flush=True)
            return
        for idx in range(found):
            S = [out_buf[idx * 7 + k] for k in range(7)]
            cl = [E(S[p], S[q]) for p in range(7) for q in range(p + 1, 7)]
            solver.add_clause(cl)
        cuts += found
        if it <= 5 or it % 50 == 0:
            print(f"  iter={it:4d} cuts={cuts:6d} edges={ec} t={time.time()-t0:.1f}s", flush=True)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["k19", "vdc"], required=True)
    ap.add_argument("--ordering", default="")
    ap.add_argument("--max-time", type=float, default=1200.0)
    ap.add_argument("--out", default="result.json")
    args = ap.parse_args()
    if args.mode == "k19":
        solve_k19_5color(args.max_time, args.out)
    else:
        a = tuple(int(z) for z in args.ordering.split(","))
        solve_ordering_vdc(a, args.max_time, args.out)
