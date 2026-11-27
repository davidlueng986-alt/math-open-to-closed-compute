from ortools.sat.python import cp_model
import itertools, time, sys

def load_links():
    links = {}
    with open("erdos151_exp4/mc37_links.txt") as f:
        for line in f:
            p = line.split()
            lid, e, ds, code, tri, k4, alpha = int(p[0]), int(p[1]), p[2], int(p[3]), int(p[4]), int(p[5]), int(p[6])
            adj = [[0]*8 for _ in range(8)]
            bit = 0
            for i in range(8):
                for j in range(i+1, 8):
                    if (code >> bit) & 1:
                        adj[i][j] = adj[j][i] = 1
                    bit += 1
            links[lid] = (e, ds, adj, tri, k4, alpha, code)
    return links

def get_auts(adj):
    degs = [sum(row) for row in adj]
    auts = []
    for p in itertools.permutations(range(8)):
        ok = True
        for i in range(8):
            if degs[p[i]] != degs[i]: ok = False; break
            for j in range(i+1, 8):
                if adj[i][j] != adj[p[i]][p[j]]: ok = False; break
            if not ok: break
        if ok: auts.append(p)
    return auts

def verify_beta_ge_3_all_6v():
    # Exhaustively verify EVERY labeled graph on 6 vertices (2^15 = 32768) has beta(H) >= 3!
    # beta(H) >= 3 iff there exists a 3-subset S of {0..5} containing NO maximal clique of H of size >= 2.
    # For a 3-subset S, the only cliques of size >= 2 inside S are edges or S itself (if triangle).
    # An edge {a,b} in S is a maximal clique iff no vertex outside {a,b} is adjacent to both a and b.
    # A triangle S is a maximal clique iff no vertex outside S is adjacent to all 3 of S.
    ok_cnt = 0
    for mask in range(1 << 15):
        adj = [0]*6
        bit = 0
        for i in range(6):
            for j in range(i+1, 6):
                if (mask >> bit) & 1:
                    adj[i] |= (1 << j); adj[j] |= (1 << i)
                bit += 1
        found = False
        for a, b, c in itertools.combinations(range(6), 3):
            # Check if {a,b,c} contains any maximal clique of size >= 2
            bad = False
            e_ab = (adj[a] >> b) & 1
            e_ac = (adj[a] >> c) & 1
            e_bc = (adj[b] >> c) & 1
            if e_ab and e_ac and e_bc:
                # Triangle {a,b,c}: maximal iff no other vertex adj to all 3
                if (adj[a] & adj[b] & adj[c]) == 0:
                    bad = True
            else:
                if e_ab and (adj[a] & adj[b]) == 0: bad = True
                if e_ac and (adj[a] & adj[c]) == 0: bad = True
                if e_bc and (adj[b] & adj[c]) == 0: bad = True
            if not bad:
                found = True; break
        if found: ok_cnt += 1
    print(f"EXHAUSTIVE 6-VERTEX LEMMA: {ok_cnt}/32768 labeled 6-vertex graphs satisfy beta(H) >= 3", flush=True)
    assert ok_cnt == 32768

links = load_links()
auts_map = {lid: get_auts(links[lid][2]) for lid in [0,1,2,3,4,6,7,8,9,19]}

def build_templates(adj0, u, allowed):
    nb = [w for w in range(8) if adj0[u][w]]
    k = len(nb)
    r = 7 - k
    templates = []
    for lid in allowed:
        adjL = links[lid][2]
        degL = [sum(row) for row in adjL]
        seen = set()
        for p0 in range(8):
            if degL[p0] != k: continue
            nL0 = [q for q in range(8) if adjL[p0][q]]
            for perm in itertools.permutations(nL0):
                ok = True
                for i in range(k):
                    for j in range(i+1, k):
                        if adj0[nb[i]][nb[j]] != adjL[perm[i]][perm[j]]:
                            ok = False; break
                    if not ok: break
                if not ok: continue
                best = min((aut[p0], tuple(aut[x] for x in perm)) for aut in auts_map[lid])
                if best in seen: continue
                seen.add(best)
                fixed = {p0} | set(perm)
                rem = [q for q in range(8) if q not in fixed]
                adj_sw = [[adjL[rem[s]][perm[i]] for i in range(k)] for s in range(r)]
                adj_ss = [[adjL[rem[s1]][rem[s2]] for s2 in range(r)] for s1 in range(r)]
                templates.append((lid, adj_sw, adj_ss))
    return nb, templates

def solve_exact_2ball(root, allowed, min_n2=21, use_s7=True, time_limit=180.0):
    e0, ds0, adj0, tri0, k40, alpha0, _ = links[root]
    deg0 = [sum(adj0[i]) for i in range(8)]
    rem0 = [7 - deg0[i] for i in range(8)]
    M = min(31, sum(rem0))
    model = cp_model.CpModel()
    x = [[model.NewBoolVar(f"x_{u}_{y}") for y in range(M)] for u in range(8)]
    a = [model.NewBoolVar(f"a_{y}") for y in range(M)]
    for y in range(M):
        model.Add(sum(x[u][y] for u in range(8)) >= a[y])
        model.Add(sum(x[u][y] for u in range(8)) <= 8 * a[y])
    col_val = [model.NewIntVar(0, 255, f"cv_{y}") for y in range(M)]
    for y in range(M):
        model.Add(col_val[y] == sum((1 << u) * x[u][y] for u in range(8)))
        if y > 0:
            model.Add(a[y-1] >= a[y])
            model.Add(col_val[y-1] >= col_val[y])
    model.Add(sum(a) >= min_n2)
    for u in range(8):
        model.Add(sum(x[u][y] for y in range(M)) == rem0[u])
    for u in range(8):
        for w in range(u+1, 8):
            if adj0[u][w]:
                known_cn = 1 + sum(adj0[u][k] * adj0[w][k] for k in range(8))
                lo = max(0, 2 - known_cn)
                hi = 4 - known_cn
                cns = []
                for y in range(M):
                    v = model.NewBoolVar(f"cn_{u}_{w}_{y}")
                    model.AddMultiplicationEquality(v, [x[u][y], x[w][y]])
                    cns.append(v)
                model.Add(sum(cns) >= lo)
                model.Add(sum(cns) <= hi)
    if use_s7:
        for skip in range(8):
            cov = [model.NewBoolVar(f"cov_{skip}_{y}") for y in range(M)]
            for y in range(M):
                others = [x[u][y] for u in range(8) if u != skip]
                model.Add(sum(others) >= cov[y])
                model.Add(sum(others) <= 7 * cov[y])
            model.Add(sum(cov) >= 19)
    e_n2 = {}
    for y in range(M):
        for z in range(y+1, M):
            v = model.NewBoolVar(f"e_{y}_{z}")
            model.Add(v <= a[y])
            model.Add(v <= a[z])
            e_n2[(y, z)] = v
    for u in range(8):
        nb, templates = build_templates(adj0, u, allowed)
        k, r, T = len(nb), rem0[u], len(templates)
        pick = [model.NewBoolVar(f"p_{u}_{t}") for t in range(T)]
        model.AddExactlyOne(pick)
        m = [[model.NewBoolVar(f"m_{u}_{s}_{y}") for y in range(M)] for s in range(r)]
        for s in range(r): model.AddExactlyOne(m[s])
        for y in range(M): model.Add(x[u][y] == sum(m[s][y] for s in range(r)))
        for s in range(r):
            for i in range(k):
                asw = model.NewBoolVar(f"asw_{u}_{s}_{i}")
                model.Add(asw == sum(pick[t] for t in range(T) if templates[t][1][s][i] == 1))
                w = nb[i]
                for y in range(M): model.Add(x[w][y] == asw).OnlyEnforceIf(m[s][y])
        for s1 in range(r):
            for s2 in range(s1+1, r):
                ass = model.NewBoolVar(f"ass_{u}_{s1}_{s2}")
                model.Add(ass == sum(pick[t] for t in range(T) if templates[t][2][s1][s2] == 1))
                for y in range(M):
                    for z in range(y+1, M):
                        model.Add(e_n2[(y, z)] == ass).OnlyEnforceIf([m[s1][y], m[s2][z]])
                        model.Add(e_n2[(y, z)] == ass).OnlyEnforceIf([m[s1][z], m[s2][y]])
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = 4
    t0 = time.time()
    status = solver.Solve(model)
    dt = time.time() - t0
    sname = solver.StatusName(status)
    n2_val = sum(solver.Value(v) for v in a) if status in (cp_model.OPTIMAL, cp_model.FEASIBLE) else -1
    print(f"ID={root:2d} (allowed={allowed}, s7={use_s7}) | status={sname:10s} |N_2|={n2_val:2d} time={dt:.2f}s", flush=True)
    return sname

if __name__ == "__main__":
    verify_beta_ge_3_all_6v()
    print("=== POSITIVE CONTROLS ===", flush=True)
    assert solve_exact_2ball(2, [2], min_n2=20, use_s7=False, time_limit=30.0) in ("OPTIMAL", "FEASIBLE")
    assert solve_exact_2ball(19, [19], min_n2=15, use_s7=False, time_limit=30.0) in ("OPTIMAL", "FEASIBLE")
    print("=== ITERATIVE ELIMINATION OF 7 OF 9 LINKS IN F_9 ===", flush=True)
    alive = [0,1,2,3,4,6,7,8,9]
    for root in [8, 9, 4, 6, 7, 3, 0]:
        st = solve_exact_2ball(root, alive, min_n2=21, use_s7=True, time_limit=120.0)
        assert st == "INFEASIBLE", f"Failed to kill ID={root}!"
        alive.remove(root)
    print(f"ALL 7 KILLED! REMAINING ALIVE: {alive}", flush=True)
