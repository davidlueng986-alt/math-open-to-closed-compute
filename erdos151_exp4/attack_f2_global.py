from ortools.sat.python import cp_model
import time, sys

# Search for ANY 8-regular {1, 2}-local graph on n in {30, 33, 36, 39} with |B_2(v)| >= 30!
# Necessary & sufficient conditions for {1, 2}-local:
# - Every vertex has degree 8, 4 Heavy edges (cn=3), 4 Light edges (cn=2), K_4-free.
# - Vertex 0 has link ID=2 on {1..8} (since 2*n_2 >= n_1 => n_2 >= 1).
# - At every vertex i:
#   - if type ID=1 (t2[i]=0): 0 Light-Light edges in L_i, 2 Heavy-Heavy edges in L_i, 8 Heavy-Light edges.
#   - if type ID=2 (t2[i]=1): 2 Light-Light edges in L_i, 4 Heavy-Heavy edges in L_i, 4 Heavy-Light edges.
#   - Also: in ID=1, each Light neighbor has 0 Light neighbors in L_i; in ID=2, each Light neighbor has 1 Light neighbor in L_i.
#   - And total edges in L_i = 10.
# - For n=30: |B_2(v)| >= 30 iff diameter <= 2 (every non-edge has >= 1 common neighbor!).

def solve_global_f2(n, time_limit=180.0):
    print(f"=== GLOBAL {{1, 2}}-LOCAL SEARCH ON n={n} (|B_2(v)| >= 30) ===", flush=True)
    model = cp_model.CpModel()
    A = [[None]*n for _ in range(n)]
    H = [[None]*n for _ in range(n)]
    L = [[None]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            a = model.NewBoolVar(f"a_{i}_{j}")
            h = model.NewBoolVar(f"h_{i}_{j}")
            l = model.NewBoolVar(f"l_{i}_{j}")
            model.Add(a == h + l)
            A[i][j] = A[j][i] = a
            H[i][j] = H[j][i] = h
            L[i][j] = L[j][i] = l

    t2 = [model.NewBoolVar(f"t2_{i}") for i in range(n)]

    # Fix vertex 0 to have link ID=2 on {1..8}:
    # ID=2 edges on 0..7 -> vertices 1..8:
    # Heavy (deg 3): 1,2,3,4 forming C_4: (1,2),(1,3),(2,4),(3,4)
    # Light (deg 2): 5,6,7,8 forming (5,8),(6,7)
    # Cross: (1,8),(2,7),(3,6),(4,5)
    id2_edges = {(1,2),(1,3),(1,8),(2,4),(2,7),(3,4),(3,6),(4,5),(5,8),(6,7)}
    model.Add(t2[0] == 1)
    for j in range(1, n):
        if j <= 8:
            model.Add(A[0][j] == 1)
            if j <= 4: model.Add(H[0][j] == 1)
            else: model.Add(L[0][j] == 1)
        else:
            model.Add(A[0][j] == 0)
    for i in range(1, 9):
        for j in range(i+1, 9):
            model.Add(A[i][j] == (1 if (i, j) in id2_edges else 0))

    # 8-regular, 4 Heavy, 4 Light at every vertex
    for i in range(n):
        model.Add(sum(H[i][j] for j in range(n) if j != i) == 4)
        model.Add(sum(L[i][j] for j in range(n) if j != i) == 4)

    # Triangle indicators tri[i,j,k] for i < j < k (only need for common neighbors)
    # Better: cn_ijk[i][j][k] = A[i][k] AND A[j][k]
    cn = {}
    for i in range(n):
        for j in range(i+1, n):
            c_list = []
            for k in range(n):
                if k == i or k == j: continue
                v = model.NewBoolVar(f"c_{i}_{j}_{k}")
                model.AddBoolAnd([A[i][k], A[j][k]]).OnlyEnforceIf(v)
                model.AddBoolOr([A[i][k].Not(), A[j][k].Not()]).OnlyEnforceIf(v.Not())
                c_list.append(v)
            cn[(i, j)] = c_list
            s = sum(c_list)
            model.Add(s == 3).OnlyEnforceIf(H[i][j])
            model.Add(s == 2).OnlyEnforceIf(L[i][j])
            if n == 30:
                # |B_2(v)| >= 30 on n=30 means diameter <= 2!
                model.Add(s >= 1).OnlyEnforceIf(A[i][j].Not())

    # For n > 30: enforce |B_2(0)| >= 30 (at least 21 vertices in 9..n-1 adjacent to {1..8})
    if n > 30:
        b2_0 = []
        for y in range(9, n):
            v = model.NewBoolVar(f"b20_{y}")
            model.Add(sum(A[u][y] for u in range(1, 9)) >= v)
            model.Add(sum(A[u][y] for u in range(1, 9)) <= 8 * v)
            b2_0.append(v)
        model.Add(sum(b2_0) >= 21)

    # Enforce K_4-free AND exact (H,H)/(L,L) counts at each vertex!
    # For each edge (j, k) and vertex i:
    # - LL_tri(i; j, k) = L[i][j] AND L[i][k] AND A[j][k]
    # - HH_tri(i; j, k) = H[i][j] AND H[i][k] AND A[j][k]
    # Note: sum_{j<k} A[i][j]*A[i][k]*A[j][k] is ALREADY 10 because sum_{j in N(i)} cn(i,j) = 4*3 + 4*2 = 20 = 2*e(L_i)!
    for i in range(n):
        ll_list = []
        hh_list = []
        for j in range(n):
            if j == i: continue
            for k in range(j+1, n):
                if k == i: continue
                ll = model.NewBoolVar(f"ll_{i}_{j}_{k}")
                model.AddBoolAnd([L[i][j], L[i][k], A[j][k]]).OnlyEnforceIf(ll)
                model.AddBoolOr([L[i][j].Not(), L[i][k].Not(), A[j][k].Not()]).OnlyEnforceIf(ll.Not())
                ll_list.append(ll)
                hh = model.NewBoolVar(f"hh_{i}_{j}_{k}")
                model.AddBoolAnd([H[i][j], H[i][k], A[j][k]]).OnlyEnforceIf(hh)
                model.AddBoolOr([H[i][j].Not(), H[i][k].Not(), A[j][k].Not()]).OnlyEnforceIf(hh.Not())
                hh_list.append(hh)
        model.Add(sum(ll_list) == 2 * t2[i])
        model.Add(sum(hh_list) == 2 + 2 * t2[i])

    # Pure ID=2 has no graph with |B_2|>=30 (already proved), so require at least one ID=1 vertex:
    model.Add(sum(t2) <= n - 1)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = 4
    t0 = time.time()
    status = solver.Solve(model)
    dt = time.time() - t0
    print(f"n={n}: status={solver.StatusName(status)} time={dt:.2f}s", flush=True)
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        n2_cnt = sum(solver.Value(v) for v in t2)
        print(f"  FOUND CANDIDATE! n1={n-n2_cnt}, n2={n2_cnt}", flush=True)

if __name__ == "__main__":
    n_arg = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    solve_global_f2(n_arg, time_limit=300.0)
