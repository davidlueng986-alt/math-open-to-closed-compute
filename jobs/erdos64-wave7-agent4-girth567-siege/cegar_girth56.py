import ctypes
import json
import os
import random
import sys
import time
from ortools.sat.python import cp_model

here = os.path.dirname(os.path.abspath(__file__))
lib = ctypes.CDLL(os.path.join(here, "libtseg_oracle.so"))
lib.find_pow2_cycles.argtypes = [
    ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int),
    ctypes.POINTER(ctypes.c_int), ctypes.c_int, ctypes.c_int,
    ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int),
]
lib.find_pow2_cycles.restype = ctypes.c_int

PAIR_TABLE = [[-1, 0, 1, 2], [0, -1, 2, 1], [1, 2, -1, 0], [2, 1, 0, -1]]

def graph_girth(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    best = 10**9
    for s in range(n):
        dist = [-1] * n; par = [-1] * n
        q = [s]; dist[s] = 0
        for u in q:
            if 2 * dist[u] + 1 >= best: break
            for w in adj[u]:
                if dist[w] == -1:
                    dist[w] = dist[u] + 1; par[w] = u; q.append(w)
                elif par[u] != w:
                    best = min(best, dist[u] + dist[w] + 1)
    return best

def build_robertson():
    m = cp_model.CpModel()
    n = 19
    e = {(i,j): m.NewBoolVar(f"e_{i}_{j}") for i in range(n) for j in range(i+1, n)}
    def E(i,j): return e[(i,j)] if i < j else e[(j,i)]
    tree = [(0,1),(0,2),(0,3),(0,4),(1,5),(1,6),(1,7),(2,8),(2,9),(2,10),(3,11),(3,12),(3,13),(4,14),(4,15),(4,16)]
    tset = set(tree)
    for (u,v) in tree: m.Add(E(u,v) == 1)
    for u in range(5):
        for v in range(u+1, n):
            if (u,v) not in tset: m.Add(E(u,v) == 0)
    for u in range(n): m.Add(sum(E(u,v) for v in range(n) if v != u) == 4)
    for i in range(5, n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                m.Add(E(i,j) + E(j,k) + E(i,k) <= 2)
    for u in range(n):
        for v in range(u+1, n):
            cn = []
            for w in range(n):
                if w != u and w != v:
                    b = m.NewBoolVar("")
                    m.AddBoolAnd([E(u,w), E(v,w)]).OnlyEnforceIf(b)
                    m.AddBoolOr([E(u,w).Not(), E(v,w).Not()]).OnlyEnforceIf(b.Not())
                    cn.append(b)
            m.Add(sum(cn) <= 1)
    solver = cp_model.CpSolver()
    solver.Solve(m)
    return n, [(i,j) for (i,j), var in e.items() if solver.Value(var) == 1]

def build_pg2_3():
    pts = []
    for x in range(3):
        for y in range(3):
            for z in range(3):
                if (x,y,z) == (0,0,0): continue
                c = x or y or z
                inv = 1 if c == 1 else 2
                nv = ((x*inv)%3, (y*inv)%3, (z*inv)%3)
                if nv not in pts: pts.append(nv)
    edges = []
    for i in range(13):
        for j in range(13):
            if (pts[i][0]*pts[j][0] + pts[i][1]*pts[j][1] + pts[i][2]*pts[j][2]) % 3 == 0:
                edges.append((i, 13+j))
    return 26, edges

def gen_high_girth_4reg(n, target_girth, bipartite, seed):
    rng = random.Random(seed)
    for restart in range(25):
        has = [[False]*n for _ in range(n)]
        ok = False
        for _ in range(300):
            has = [[False]*n for _ in range(n)]
            ok = True
            if bipartite:
                half = n // 2
                L = [i for i in range(half) for _ in range(4)]
                R = [half + i for i in range(half) for _ in range(4)]
                rng.shuffle(R)
                for u, v in zip(L, R):
                    if has[u][v]: ok = False; break
                    has[u][v] = has[v][u] = True
            else:
                stubs = [i for i in range(n) for _ in range(4)]
                rng.shuffle(stubs)
                for i in range(0, len(stubs), 2):
                    u, v = stubs[i], stubs[i+1]
                    if u == v or has[u][v]: ok = False; break
                    has[u][v] = has[v][u] = True
            if ok: break
        if not ok: continue

        def cost_fn():
            adj = [[j for j in range(n) if has[i][j]] for i in range(n)]
            c3 = 0
            if not bipartite:
                for u in range(n):
                    for v in adj[u]:
                        if v > u:
                            for w in adj[v]:
                                if w > v and has[u][w]: c3 += 1
            c4 = 0
            for u in range(n):
                for w in range(u+1, n):
                    cn = sum(1 for v in adj[u] if has[v][w])
                    c4 += cn * (cn - 1) // 2
            return 10 * c3 + c4 // 2

        cost = cost_fn()
        for step in range(3000):
            if cost == 0:
                edges = [(i,j) for i in range(n) for j in range(i+1, n) if has[i][j]]
                if graph_girth(n, edges) >= target_girth:
                    return edges
                break
            es = [(i,j) for i in range(n) for j in range(i+1, n) if has[i][j]]
            a, b = rng.choice(es); c, d = rng.choice(es)
            if len({a, b, c, d}) < 4: continue
            if not bipartite and rng.getrandbits(1): c, d = d, c
            u1, v1 = a, (d if bipartite else c)
            u2, v2 = (c if bipartite else b), (b if bipartite else d)
            if has[u1][v1] or has[u2][v2]: continue
            has[a][b] = has[b][a] = has[c][d] = has[d][c] = False
            has[u1][v1] = has[v1][u1] = has[u2][v2] = has[v2][u2] = True
            ncost = cost_fn()
            if ncost <= cost or (ncost <= cost + 2 and rng.randrange(25) == 0):
                cost = ncost
            else:
                has[u1][v1] = has[v1][u1] = has[u2][v2] = has[v2][u2] = False
                has[a][b] = has[b][a] = has[c][d] = has[d][c] = True
    return None

def run_cegar(name, n, edges, time_limit=120.0):
    t0 = time.time()
    g = graph_girth(n, edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    for v in range(n): adj[v].sort()
    deg_arr = (ctypes.c_int * n)(*[len(adj[v]) for v in range(n)])
    adj_flat = (ctypes.c_int * (4*n))()
    for v in range(n):
        for i, w in enumerate(adj[v]): adj_flat[v*4 + i] = w
    nbr_pos = [{w: i for i, w in enumerate(adj[v])} for v in range(n)]

    model = cp_model.CpModel()
    p_eq = []
    for v in range(n):
        d = len(adj[v])
        if d == 4:
            bs = [model.NewBoolVar(f"p_{v}_{k}") for k in range(3)]
            model.AddExactlyOne(bs)
            p_eq.append(bs)
        elif d == 2:
            b = model.NewBoolVar(f"s_{v}")
            p_eq.append([b.Not(), b])
        else:
            raise ValueError(f"bad deg {d}")

    clauses = 0; iters = 0
    out_len = (ctypes.c_int * 64)()
    out_verts = (ctypes.c_int * (64*64))()

    def add_cycle_clause(cyc, p_vals):
        nonlocal clauses
        L = len(cyc); lits = []
        for idx in range(L):
            v = cyc[idx]; u = cyc[(idx - 1) % L]; w = cyc[(idx + 1) % L]
            if len(adj[v]) == 4:
                pt = PAIR_TABLE[nbr_pos[v][u]][nbr_pos[v][w]]
                lits.append(p_eq[v][pt].Not() if p_vals[v] == pt else p_eq[v][pt])
            else:
                lits.append(p_eq[v][1] if p_vals[v] == 0 else p_eq[v][0])
        model.AddBoolOr(lits)
        clauses += 1

    rng = random.Random(42)
    for _ in range(20):
        pv = [rng.randrange(3 if len(adj[v])==4 else 2) for v in range(n)]
        p_arr = (ctypes.c_int * n)(*pv)
        cnt = lib.find_pow2_cycles(n, deg_arr, adj_flat, p_arr, min(n, 10), 25, out_len, out_verts)
        for k in range(cnt):
            L = out_len[k]
            add_cycle_clause([out_verts[k*64 + i] for i in range(L)], pv)

    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 4

    while True:
        rem = time_limit - (time.time() - t0)
        if rem <= 0:
            res = {"name": name, "n": n, "girth": g, "verdict": "TIMEOUT", "iters": iters, "clauses": clauses, "time_s": round(time.time()-t0, 2)}
            print(res, flush=True); return res
        solver.parameters.max_time_in_seconds = rem
        status = solver.Solve(model)
        if status == cp_model.INFEASIBLE:
            res = {"name": name, "n": n, "girth": g, "verdict": "UNSAT", "iters": iters, "clauses": clauses, "time_s": round(time.time()-t0, 2)}
            print(res, flush=True); return res
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            res = {"name": name, "n": n, "girth": g, "verdict": "TIMEOUT", "iters": iters, "clauses": clauses, "time_s": round(time.time()-t0, 2)}
            print(res, flush=True); return res
        pv = [next(k for k in range(3) if solver.Value(p_eq[v][k]) == 1) if len(adj[v])==4 else solver.Value(p_eq[v][1]) for v in range(n)]
        p_arr = (ctypes.c_int * n)(*pv)
        cnt = 0
        for cap in [8, 12, 16, n]:
            if cap > n: cap = n
            cnt = lib.find_pow2_cycles(n, deg_arr, adj_flat, p_arr, cap, 32, out_len, out_verts)
            if cnt > 0 or cap == n: break
        if cnt == 0:
            res = {"name": name, "n": n, "girth": g, "verdict": "COUNTEREXAMPLE", "p": pv, "iters": iters, "clauses": clauses, "time_s": round(time.time()-t0, 2)}
            print("!!!", res, flush=True); return res
        for k in range(cnt):
            L = out_len[k]
            add_cycle_clause([out_verts[k*64 + i] for i in range(L)], pv)
        iters += 1

def main():
    out_path = sys.argv[1] if len(sys.argv) > 1 else "cegar_girth56.json"
    results = []
    n_rob, e_rob = build_robertson()
    results.append(run_cegar("Robertson_cage_4_5", n_rob, e_rob, 120.0))
    u, v = e_rob[0]
    results.append(run_cegar("Robertson_1port_sub", n_rob + 1, [e for e in e_rob if e != (u,v)] + [(u, n_rob), (v, n_rob)], 120.0))

    for n, seed in [(20, 701), (21, 702), (22, 703), (23, 704), (24, 705), (25, 706), (26, 707)]:
        es = gen_high_girth_4reg(n, 5, False, seed)
        if es:
            results.append(run_cegar(f"Girth5_4reg_n{n}", n, es, 120.0))
            if n in (22, 24):
                u, v = es[0]
                results.append(run_cegar(f"Girth5_1port_n{n+1}", n + 1, [e for e in es if e != (u,v)] + [(u, n), (v, n)], 120.0))

    n_pg, e_pg = build_pg2_3()
    results.append(run_cegar("PG2_3_cage_4_6", n_pg, e_pg, 180.0))
    u, v = e_pg[0]
    results.append(run_cegar("PG2_3_1port_sub", n_pg + 1, [e for e in e_pg if e != (u,v)] + [(u, n_pg), (v, n_pg)], 180.0))

    for n, seed in [(28, 801), (30, 802), (32, 803)]:
        es = gen_high_girth_4reg(n, 6, True, seed)
        if es:
            results.append(run_cegar(f"Girth6_Bip4reg_n{n}", n, es, 180.0))

    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Wrote {len(results)} CEGAR results to {out_path}")

if __name__ == "__main__":
    main()
