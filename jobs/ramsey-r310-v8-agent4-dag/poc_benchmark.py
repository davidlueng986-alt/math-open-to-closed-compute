#!/usr/bin/env python3
"""
Head-to-head OR-Tools CP-SAT PoC benchmark:
Compares v7 Adjacent-Root vs V8 Non-Adjacent-Root (Tier 1 D6 Inner-WM)
on the exact surviving degree-6 profile n = (1, 0, 1, 38), m = 178.
"""
import itertools, time, random
from ortools.sat.python import cp_model

N = 40
E9 = {6: 118, 7: 104, 8: 95, 9: 86}
E8 = {21: 35, 22: 42, 23: 49, 24: 56, 25: 65, 26: 73, 27: 85}
ET9 = {23: 35, 24: 40, 25: 46, 26: 52, 27: 61, 28: 68}

def bits(x):
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b

def find_indep_sets(adj, verts, k, limit=256, rng=None):
    order = list(verts)
    if rng: rng.shuffle(order)
    inv = {v: i for i, v in enumerate(order)}
    b = [sum(1 << inv[j] for j in bits(adj[v]) if j in inv) for v in order]
    out = []
    def go(p, rem, s):
        if len(out) >= limit: return
        if rem == 0:
            out.append(tuple(sorted(s)))
            return
        while p.bit_count() >= rem and len(out) < limit:
            x = p & -p
            p ^= x
            i = x.bit_length() - 1
            go(p & ~b[i], rem - 1, s + [order[i]])
    go((1 << len(order)) - 1, k, [])
    return out

def solve_cpsat_profile(mode, profile, m, params, time_limit=10.0):
    t0 = time.monotonic()
    model = cp_model.CpModel()
    E = {(i, j): model.NewBoolVar(f"e_{i}_{j}") for i in range(N) for j in range(i + 1, N)}
    def edge(i, j): return E[(i, j)] if i < j else E[(j, i)]

    if mode == 'v7_adj':
        d, q = params
        X = list(range(2, d + 1)); Y = list(range(d + 1, d + q)); T = list(range(d + q, N))
        A = [1] + X; B = [0] + Y; H0 = Y + T; H1 = X + T
        for v in range(1, N): model.Add(edge(0, v) == (1 if v in A else 0))
        for v in range(2, N): model.Add(edge(1, v) == (1 if v in B else 0))
        for C in (A, B):
            for i, j in itertools.combinations(C, 2): model.Add(edge(i, j) == 0)
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(H0, 2)) >= E9[d])
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(H0, 2)) <= 180 - 9 * d)
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(H1, 2)) >= E9[q])
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(H1, 2)) <= 4 * len(H1))
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(T, 2)) >= ET9[len(T)])
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(T, 2)) <= 4 * len(T))
        for H, k in [(H0, d), (H1, q)]:
            for v in H:
                s = sum(edge(v, u) for u in H if u != v)
                model.Add(s >= 11 - k); model.Add(s <= 8)
        for v in X: model.Add(sum(edge(v, u) for u in range(N) if u != v) >= q)
        deg0, deg1 = d, q
        sep_targets = [(H0, 9, (0,)), (H1, 9, (1,)), (list(range(N)), 10, ())]
        free_vars_est = 780 - (39 + 38 + d*(d-1)//2 + q*(q-1)//2)
    else:
        du, dv, c, eT_cap = params
        nx, ny = du - c, dv - c
        S = list(range(2, 2 + c)); X = list(range(2 + c, 2 + du))
        Y = list(range(2 + du, 2 + du + ny)); T = list(range(2 + du + ny, N))
        A = S + X; B = S + Y; H0 = [1] + Y + T; H1 = [0] + X + T
        for v in range(1, N): model.Add(edge(0, v) == (1 if v in A else 0))
        for v in range(2, N): model.Add(edge(1, v) == (1 if v in B else 0))
        for i, j in itertools.combinations(A, 2): model.Add(edge(i, j) == 0)
        for i, j in itertools.combinations(B, 2):
            if not (i in S and j in S): model.Add(edge(i, j) == 0)
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(H0, 2)) >= E9[du])
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(H0, 2)) <= (7 * len(H0) + du * (10 - du)) // 2)
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(H1, 2)) >= E9[dv])
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(H1, 2)) <= (7 * len(H1) + dv * (10 - dv)) // 2)
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(T, 2)) >= E8[len(T)])
        model.Add(sum(edge(i, j) for i, j in itertools.combinations(T, 2)) <= eT_cap)
        for v in T:
            st = sum(edge(v, u) for u in T if u != v)
            model.Add(st >= len(T) - 23); model.Add(st <= 7)
        for x in X: model.Add(sum(edge(x, y) for y in Y) >= 1)
        for y in Y: model.Add(sum(edge(x, y) for x in X) >= 1)
        for H, k in [(H0, du), (H1, dv)]:
            for v in H:
                s = sum(edge(v, u) for u in H if u != v)
                model.Add(s >= 11 - k); model.Add(s <= 8)
        deg0, deg1 = du, dv
        sep_targets = [(T, 8, (0, 1)), (H0, 9, (0,)), (H1, 9, (1,)), (list(range(N)), 10, ())]
        free_vars_est = 780 - (39 + 38 + du*(du-1)//2 + dv*(dv-1)//2 - c*(c-1)//2)

    for i, j, k in itertools.combinations(range(N), 3):
        model.Add(edge(i, j) + edge(i, k) + edge(j, k) <= 2)
    degs = [sum(edge(i, j) for j in range(N) if j != i) for i in range(N)]
    model.Add(degs[0] == deg0); model.Add(degs[1] == deg1)
    is_deg = {}
    for i in range(N):
        model.Add(degs[i] >= 6); model.Add(degs[i] <= 9)
        for k in (6, 7, 8, 9):
            b = model.NewBoolVar(f"d_{i}_{k}")
            model.Add(degs[i] == k).OnlyEnforceIf(b)
            model.Add(degs[i] != k).OnlyEnforceIf(b.Not())
            is_deg[(i, k)] = b
        model.Add(sum(is_deg[(i, k)] for k in (6, 7, 8, 9)) == 1)
    for idx, k in enumerate((6, 7, 8, 9)):
        model.Add(sum(is_deg[(i, k)] for i in range(N)) == profile[idx])
    model.Add(sum(E.values()) == m)
    for v in range(2, N):
        if v not in A: model.Add(sum(edge(v, u) for u in A) >= 1)
        if v not in B: model.Add(sum(edge(v, u) for u in B) >= 1)

    rng = random.Random(42)
    models_found = total_cuts = i8_cuts = total_conflicts = total_branches = 0
    status_str = "TIMEOUT"
    while time.monotonic() - t0 < time_limit:
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = max(0.1, time_limit - (time.monotonic() - t0))
        solver.parameters.num_search_workers = 4
        st = solver.Solve(model)
        total_conflicts += solver.NumConflicts(); total_branches += solver.NumBranches()
        if st == cp_model.INFEASIBLE:
            status_str = "UNSAT"; break
        elif st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            models_found += 1
            adj = [0] * N
            for (i, j), var in E.items():
                if solver.Value(var): adj[i] |= (1 << j); adj[j] |= (1 << i)
            bad = set()
            for verts, k, pref in sep_targets:
                for s in find_indep_sets(adj, verts, k, 64, rng):
                    full = tuple(sorted(pref + s))
                    if full not in bad:
                        bad.add(full)
                        if k == 8: i8_cuts += 1
            if not bad:
                status_str = "WITNESS_FOUND"; break
            for s in bad:
                model.Add(sum(edge(i, j) for i, j in itertools.combinations(s, 2)) >= 1)
                total_cuts += 1
        else:
            status_str = "TIMEOUT"; break
    return dict(mode=mode, params=params, free_edges=free_vars_est, status=status_str,
                elapsed=round(time.monotonic() - t0, 3), models=models_found, cuts=total_cuts,
                i8_cuts=i8_cuts, conflicts=total_conflicts, branches=total_branches)

if __name__ == "__main__":
    print("=== HEAD-TO-HEAD CP-SAT PoC ON PROFILE n=(1, 0, 1, 38), m=178 ===")
    for p in [(6, 9), (6, 8)]:
        print(" ", solve_cpsat_profile('v7_adj', (1, 0, 1, 38), 178, p, time_limit=10.0))
    for p in [(6, 9, 4, 92), (6, 8, 3, 92), (6, 9, 3, 84), (6, 9, 2, 76)]:
        print(" ", solve_cpsat_profile('v8_na', (1, 0, 1, 38), 178, p, time_limit=10.0))
