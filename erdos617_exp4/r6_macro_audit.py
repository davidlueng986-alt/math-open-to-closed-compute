import subprocess, time, sys, os
from concurrent.futures import ProcessPoolExecutor, as_completed
from ortools.sat.python import cp_model
from itertools import combinations

PROFILES = {
    "p6": (7,7,7,6,5,5),
    "p7": (8,6,6,6,6,5),
    "p8": (7,7,6,6,6,5),
    "p9": (7,6,6,6,6,6),
}

def e_min(n, r=6):
    q, rem = divmod(n, r)
    return rem * (q + 1) * q // 2 + (r - rem) * q * (q - 1) // 2

def gen_m_tuples(prof):
    base = [5 * e_min(a, 6) for a in prof]
    slack = 15 - sum(base)
    res = []
    def dfs(idx, rem, cur):
        if idx == 6:
            res.append(tuple(cur))
            return
        max_add = rem
        if idx > 0 and prof[idx] == prof[idx-1]:
            max_add = min(max_add, cur[-1] - base[idx])
        for add in range(max_add, -1, -1):
            dfs(idx + 1, rem - add, cur + [base[idx] + add])
    dfs(0, slack, [])
    return res

def solve_one(args):
    prof, m_vals, time_limit = args
    S = sum(a*(a-1)//2 for a in prof)
    base = [5 * e_min(a, 6) for a in prof]
    m_in = sum(m_vals)
    max_m_out = 111 - S + m_in

    U = [[0]*6 for _ in range(6)]
    M = [[0]*6 for _ in range(6)]
    for i in range(6):
        for j in range(6):
            if i == j: continue
            ub = prof[i]*prof[j] - 5*e_min(prof[i]+prof[j], 6) + m_vals[i] + m_vals[j]
            if prof[i] >= 6: ub = min(ub, prof[j]*(prof[i]-5) + (m_vals[i]-base[i]) + m_vals[j])
            if prof[j] >= 6: ub = min(ub, prof[i]*(prof[j]-5) + (m_vals[j]-base[j]) + m_vals[i])
            if prof[i] == 5 and m_vals[i] == 0:
                ec = 0
                while e_min(ec + 1, 5) <= m_vals[j]: ec += 1
                ub = min(ub, ec)
            if prof[j] == 5 and m_vals[j] == 0:
                ec = 0
                while e_min(ec + 1, 5) <= m_vals[i]: ec += 1
                ub = min(ub, ec)
            ub = max(0, min(ub, max_m_out))
            U[i][j] = ub
            mk = prof[j]
            if prof[j] >= 6: mk = min(mk, (prof[j] - 5) + (m_vals[j] - base[j]))
            mk = min(mk, ub)
            M[i][j] = mk

    model = cp_model.CpModel()
    E = {}
    for i in range(6):
        for j in range(i+1, 6):
            E[(i,j)] = E[(j,i)] = model.NewIntVar(0, U[i][j], f"E_{i}_{j}")

    for r_sz in range(2, 7):
        for T in combinations(range(6), r_sz):
            NT = sum(prof[i] for i in T)
            rhs = sum(prof[i]*prof[j] for i, j in combinations(T, 2)) - 5*e_min(NT, 6) + sum(m_vals[i] for i in T)
            if r_sz == 6: rhs = min(rhs, max_m_out)
            model.Add(sum(E[(i,j)] for i, j in combinations(T, 2)) <= rhs)

    E_sub_vars = {}
    E_sub_ge = {}
    def get_sub_ge(nodes_tuple, T):
        key = (nodes_tuple, T)
        if key in E_sub_ge: return E_sub_ge[key]
        if nodes_tuple not in E_sub_vars:
            ub = min(max_m_out, sum(U[a][b] for a, b in combinations(nodes_tuple, 2)))
            v = model.NewIntVar(0, ub, f"Esub_{nodes_tuple}")
            model.Add(v == sum(E[(a, b)] for a, b in combinations(nodes_tuple, 2)))
            E_sub_vars[nodes_tuple] = (v, ub)
        v, ub = E_sub_vars[nodes_tuple]
        if T > ub:
            E_sub_ge[key] = None
            return None
        b = model.NewBoolVar(f"Esub_{nodes_tuple}_ge_{T}")
        model.Add(v >= T).OnlyEnforceIf(b)
        model.Add(v < T).OnlyEnforceIf(b.Not())
        E_sub_ge[key] = b
        return b

    for i in range(6):
        if m_vals[i] == 0: continue
        ai = prof[i]
        others = [j for j in range(6) if j != i]
        inp = " ".join(map(str, prof)) + " " + " ".join(map(str, m_vals)) + f" {i}\n"
        out = subprocess.check_output(["./gen_sub_pareto"], input=inp, text=True)
        clauses = []
        for line in out.strip().splitlines():
            vals = list(map(int, line.split()))
            clauses.append((vals[0], tuple(vals[1:6]), vals[6]))

        ng = {(u,v): model.NewBoolVar(f"ng_{i}_{u}_{v}") for u,v in combinations(range(ai), 2)}
        model.Add(sum(ng.values()) == m_vals[i])
        dbar = []
        for v in range(ai):
            db = model.NewIntVar(0, ai - 1, f"db_{i}_{v}")
            model.Add(db == sum(ng[(min(v,u), max(v,u))] for u in range(ai) if u != v))
            if ai == 8:
                model.Add(db <= m_vals[i] - 5)
            dbar.append(db)
        for v in range(ai - 1):
            model.Add(dbar[v] >= dbar[v+1])

        d = {}
        for j in others:
            for v in range(ai):
                dvj = model.NewIntVar(0, M[i][j], f"d_{i}_{v}_{j}")
                d[(v, j)] = dvj
                model.Add(dvj + dbar[v] <= prof[j])
            model.Add(sum(d[(v, j)] for v in range(ai)) == E[(i, j)])
            if prof[j] >= 6:
                exs = []
                for v in range(ai):
                    ex = model.NewIntVar(0, M[i][j], f"ex_{i}_{v}_{j}")
                    model.Add(ex >= d[(v, j)] - (prof[j] - 5))
                    exs.append(ex)
                model.Add(sum(exs) <= (m_vals[j] - base[j]) + m_vals[i])

        needed_thresh = [set() for _ in range(5)]
        mask_to_nodes = {}
        for mask, c_vec, T in clauses:
            for k in range(5): needed_thresh[k].add(c_vec[k] + 1)
            if mask not in mask_to_nodes:
                mask_to_nodes[mask] = tuple(sorted(others[k] for k in range(5) if mask & (1 << k)))

        for u, v in combinations(range(ai), 2):
            c_ge = {}
            for k in range(5):
                j = others[k]
                c_uv = d[(u, j)] + d[(v, j)]
                for val in needed_thresh[k]:
                    if val > 2 * M[i][j]:
                        c_ge[(k, val)] = None
                    else:
                        b = model.NewBoolVar(f"c_{i}_{u}_{v}_{k}_ge_{val}")
                        model.Add(c_uv >= val).OnlyEnforceIf(b)
                        model.Add(c_uv < val).OnlyEnforceIf(b.Not())
                        c_ge[(k, val)] = b
            for mask, c_vec, T in clauses:
                lits = [ng[(u, v)].Not()]
                for k in range(5):
                    lit = c_ge[(k, c_vec[k] + 1)]
                    if lit is not None: lits.append(lit)
                sub_lit = get_sub_ge(mask_to_nodes[mask], T)
                if sub_lit is not None: lits.append(sub_lit)
                model.AddBoolOr(lits)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = 1
    t0 = time.time()
    st = solver.Solve(model)
    dt = time.time() - t0
    name = solver.StatusName(st)
    ev = None
    if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        ev = {f"{i}{j}": solver.Value(E[(i,j)]) for i in range(6) for j in range(i+1,6) if solver.Value(E[(i,j)]) > 0}
    return m_vals, name, dt, ev

def main():
    pkey = sys.argv[1]
    tl = float(sys.argv[2]) if len(sys.argv) > 2 else 15.0
    prof = PROFILES[pkey]
    tups = gen_m_tuples(prof)
    print(f"=== MACRO SUBSET-PARETO AUDIT: {pkey} {prof} ({len(tups)} tuples, tl={tl}s) ===", flush=True)
    t0 = time.time()
    infeas, feas, unk = [], [], []
    with ProcessPoolExecutor(max_workers=4) as ex:
        futs = {ex.submit(solve_one, (prof, mt, tl)): mt for mt in tups}
        for fut in as_completed(futs):
            mt, name, dt, ev = fut.result()
            if name == "INFEASIBLE":
                infeas.append(mt)
            elif name in ("FEASIBLE", "OPTIMAL"):
                feas.append((mt, ev))
            else:
                unk.append(mt)
    print(f"DONE {pkey} in {time.time()-t0:.1f}s: INFEASIBLE={len(infeas)}, FEASIBLE={len(feas)}, UNKNOWN={len(unk)}", flush=True)
    if feas:
        print(f"FEASIBLE ({len(feas)}):")
        for mt, ev in sorted(feas):
            print(f"  {mt} -> {ev}")
    if unk:
        print(f"UNKNOWN ({len(unk)}):")
        for mt in sorted(unk):
            print(f"  {mt}")

if __name__ == "__main__":
    main()
