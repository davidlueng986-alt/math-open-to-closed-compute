#!/usr/bin/env python3
"""OR-Tools CP-SAT PoC for Ramsey R(3,10) V8 with V8 convexity, König bound, sound degree-tuple symmetry, and C++ lazy I10 separation."""
import argparse, ctypes, itertools, json, sys, time
from pathlib import Path
from ortools.sat.python import cp_model
from reconstruct_tasks import feasible_v8

N = 40; V = (6, 7, 8, 9)
E = {6: 118, 7: 104, 8: 95, 9: 86}
ET = {23: 35, 24: 40, 25: 46, 26: 52, 27: 61, 28: 68}

libisep = ctypes.CDLL(str(Path(__file__).resolve().parent / 'libisep.so'))
libisep.find_indep_sets.argtypes = [
    ctypes.POINTER(ctypes.c_uint64), ctypes.c_uint64, ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int)
]
libisep.find_indep_sets.restype = ctypes.c_int

def find_indep(adj, verts, k, limit=256):
    arr = (ctypes.c_uint64 * 40)(*adj); mask = 0
    for v in verts: mask |= (1 << v)
    buf = (ctypes.c_int * (limit * k))()
    cnt = libisep.find_indep_sets(arr, ctypes.c_uint64(mask), k, limit, buf)
    return [tuple(sorted(buf[i * k + j] for j in range(k))) for i in range(cnt)]

def groups(d, q):
    X = list(range(2, d + 1)); Y = list(range(d + 1, d + q)); T = list(range(d + q, 40))
    return X, Y, T, [1] + X, [0] + Y

def solve_cpsat(task, time_limit=60.0, workers=2, codeg_mode='lazy', v8_allowed=None):
    t0 = time.monotonic()
    d, q, m = task['d'], task['q'], task['m']
    ns = [tuple(n) for n in task['profiles']]
    X, Y, T, A, B = groups(d, q); H0, H1 = Y + T, X + T; nx, ny, nt = len(X), len(Y), len(T)

    model = cp_model.CpModel(); fixed = {}
    for i in range(1, N): fixed[(0, i)] = 1 if i in A else 0
    for i in range(2, N): fixed[(1, i)] = 1 if i in B else 0
    for C in (A, B):
        for i, j in itertools.combinations(C, 2): fixed[(min(i, j), max(i, j))] = 0

    ev = {(i, j): fixed[(i, j)] if (i, j) in fixed else model.NewBoolVar(f'e_{i}_{j}')
          for i in range(N) for j in range(i + 1, N)}
    def Evar(i, j): return ev[(i, j) if i < j else (j, i)]
    def _is0(x): return isinstance(x, int) and x == 0
    def _is1(x): return isinstance(x, int) and x == 1

    for i, j, k in itertools.combinations(range(N), 3):
        a, b, c = Evar(i, j), Evar(i, k), Evar(j, k)
        if _is0(a) or _is0(b) or _is0(c): continue
        model.AddBoolOr([x.Not() for x in (a, b, c) if not _is1(x)])

    possible_degs = sorted({V[k] for n in ns for k in range(4) if n[k] > 0})
    deg = [None] * N; deg[0] = model.NewConstant(d); deg[1] = model.NewConstant(q)
    for i in range(2, N):
        lo = q if i in X else 6
        dom = [k for k in possible_degs if k >= lo]
        deg[i] = model.NewConstant(dom[0]) if len(dom) == 1 else model.NewIntVarFromDomain(cp_model.Domain.FromValues(dom), f'deg_{i}')
        model.Add(sum(Evar(i, j) for j in range(N) if j != i) == deg[i])

    konig_lb = max(task['tlo'], d + q - 11)
    if konig_lb > task['thi']:
        return {'task_id': task['id'], 'status': 'UNSAT_KONIG', 'wall_s': round(time.monotonic() - t0, 3)}
    t_var = model.NewIntVar(konig_lb, task['thi'], 't_XY')
    model.Add(sum(Evar(x, y) for x in X for y in Y) == t_var)
    model.Add(sum(ev[(i, j)] for i in range(N) for j in range(i + 1, N)) == m)

    cnt_vars = []
    for idx, k in enumerate(V):
        lo_k, hi_k = min(n[idx] for n in ns), max(n[idx] for n in ns)
        c_var = model.NewConstant(lo_k) if lo_k == hi_k else model.NewIntVar(lo_k, hi_k, f'n_{k}')
        inds = []
        for i in range(N):
            if i == 0:
                if d == k: inds.append(1)
            elif i == 1:
                if q == k: inds.append(1)
            else:
                dom_i = [v for v in possible_degs if v >= (q if i in X else 6)]
                if k not in dom_i: continue
                if len(dom_i) == 1: inds.append(1)
                else:
                    b = model.NewBoolVar(f'isd_{i}_{k}')
                    model.Add(deg[i] == k).OnlyEnforceIf(b); model.Add(deg[i] != k).OnlyEnforceIf(b.Not())
                    inds.append(b)
        model.Add(sum(inds) == c_var); cnt_vars.append(c_var)

    if v8_allowed is not None:
        tuples = [tuple(n_prof) + (tv,) for n_prof, t_list in v8_allowed for tv in t_list if konig_lb <= tv <= task['thi']]
        if not tuples:
            return {'task_id': task['id'], 'status': 'UNSAT_PREFILTER', 'wall_s': round(time.monotonic() - t0, 3)}
        model.AddAllowedAssignments(cnt_vars + [t_var], tuples)

    h0_max = min(180 - 9 * d, (7 * len(H0) + d * (10 - d)) // 2)
    h1_max = min(4 * len(H1), (7 * len(H1) + q * (10 - q)) // 2)
    model.AddLinearConstraint(sum(Evar(i, j) for i, j in itertools.combinations(H0, 2)), E[d], h0_max)
    model.AddLinearConstraint(sum(Evar(i, j) for i, j in itertools.combinations(H1, 2)), E[q], h1_max)
    model.AddLinearConstraint(sum(Evar(i, j) for i, j in itertools.combinations(T, 2)), ET[nt], 4 * nt)

    for v in H0: model.AddLinearConstraint(sum(Evar(v, u) for u in H0 if u != v), 11 - d, 8)
    for v in H1: model.AddLinearConstraint(sum(Evar(v, u) for u in H1 if u != v), 11 - q, 8)

    degX, degY = {}, {}
    for v in T:
        dx = model.NewIntVar(1, nx, f'dx_{v}'); dy = model.NewIntVar(1, ny, f'dy_{v}')
        model.Add(sum(Evar(v, x) for x in X) == dx); model.Add(sum(Evar(v, y) for y in Y) == dy)
        model.Add(dx <= deg[v] + d - 11); model.Add(dy <= deg[v] + q - 11)
        degX[v], degY[v] = dx, dy
    for x in X:
        dy = model.NewIntVar(0, min(ny, q - 3), f'dy_{x}')
        model.Add(sum(Evar(x, y) for y in Y) == dy); model.Add(dy <= deg[x] + q - 12); degY[x] = dy
    for y in Y:
        dx = model.NewIntVar(0, min(nx, d - 3), f'dx_{y}')
        model.Add(sum(Evar(x, y) for x in X) == dx); model.Add(dx <= deg[y] + d - 12); degX[y] = dx

    c2x_tab = [k * (k - 1) // 2 for k in range(nx + 1)]; c2y_tab = [k * (k - 1) // 2 for k in range(ny + 1)]
    c2x = [model.NewIntVar(0, c2x_tab[-1], f'c2x_{v}') for v in Y + T]
    for v, cv in zip(Y + T, c2x): model.AddElement(degX[v], c2x_tab, cv)
    model.Add(sum(c2x) <= (nx - 1) * sum(deg[x] for x in X) - 12 * (nx * (nx - 1) // 2))
    c2y = [model.NewIntVar(0, c2y_tab[-1], f'c2y_{v}') for v in X + T]
    for v, cv in zip(X + T, c2y): model.AddElement(degY[v], c2y_tab, cv)
    model.Add(sum(c2y) <= (ny - 1) * sum(deg[y] for y in Y) - 12 * (ny * (ny - 1) // 2))

    for i in range(nx - 1): model.Add(deg[X[i]] * 16 + degY[X[i]] >= deg[X[i + 1]] * 16 + degY[X[i + 1]])
    for i in range(ny - 1): model.Add(deg[Y[i]] * 16 + degX[Y[i]] >= deg[Y[i + 1]] * 16 + degX[Y[i + 1]])
    for i in range(nt - 1): model.Add(deg[T[i]] * 256 + degX[T[i]] * 16 + degY[T[i]] >= deg[T[i + 1]] * 256 + degX[T[i + 1]] * 16 + degY[T[i + 1]])

    encoded_codeg = set()
    def add_pair_codeg(i, j):
        p = (min(i, j), max(i, j))
        if p in encoded_codeg or _is1(Evar(*p)): return
        encoded_codeg.add(p); u, v = p; ws = []
        for k in range(N):
            if k in (u, v): continue
            a, b = Evar(u, k), Evar(v, k)
            if _is0(a) or _is0(b): continue
            if _is1(a) and _is1(b): ws.append(1)
            elif _is1(a): ws.append(b)
            elif _is1(b): ws.append(a)
            else:
                w = model.NewBoolVar(f'cn_{u}_{v}_{k}')
                model.AddBoolAnd([a, b]).OnlyEnforceIf(w); model.AddBoolOr([a.Not(), b.Not()]).OnlyEnforceIf(w.Not())
                ws.append(w)
        if _is0(Evar(u, v)):
            model.Add(sum(ws) >= 1); model.Add(sum(ws) <= deg[u] + deg[v] - 11)
        else:
            model.Add(sum(ws) >= 1).OnlyEnforceIf(Evar(u, v).Not())
            model.Add(sum(ws) <= deg[u] + deg[v] - 11).OnlyEnforceIf(Evar(u, v).Not())

    if codeg_mode == 'all':
        for i in range(2, N):
            for j in range(i + 1, N): add_pair_codeg(i, j)
    else:
        for i, j in itertools.combinations(X, 2): add_pair_codeg(i, j)
        for i, j in itertools.combinations(Y, 2): add_pair_codeg(i, j)

    seen_cuts = set(); models_found = 0; status_str = 'OPEN'
    while True:
        rem = time_limit - (time.monotonic() - t0)
        if rem <= 0.5: status_str = 'TIMEOUT'; break
        solver = cp_model.CpSolver(); solver.parameters.max_time_in_seconds = rem; solver.parameters.num_search_workers = workers
        st = solver.Solve(model)
        if st == cp_model.INFEASIBLE: status_str = 'UNSAT'; break
        if st not in (cp_model.FEASIBLE, cp_model.OPTIMAL): status_str = f'STOPPED_{solver.StatusName(st)}'; break
        models_found += 1; adj = [0] * N
        for i in range(N):
            for j in range(i + 1, N):
                x = ev[(i, j)]
                if (x if isinstance(x, int) else solver.Value(x)): adj[i] |= (1 << j); adj[j] |= (1 << i)
        degs = [x.bit_count() for x in adj]
        if codeg_mode == 'lazy':
            for i in range(2, N):
                for j in range(i + 1, N):
                    if (adj[i] >> j) & 1: continue
                    cn = (adj[i] & adj[j]).bit_count()
                    if cn == 0 or cn > degs[i] + degs[j] - 11: add_pair_codeg(i, j)
        bad = set()
        for ss in find_indep(adj, H0, 9, 128): bad.add(tuple(sorted((0,) + ss)))
        for ss in find_indep(adj, H1, 9, 128): bad.add(tuple(sorted((1,) + ss)))
        if len(bad) < 64:
            for ss in find_indep(adj, range(N), 10, 256): bad.add(ss)
        if not bad:
            chk = find_indep(adj, range(N), 10, 1)
            if not chk: status_str = 'WITNESS_FOUND'; break
            bad.add(chk[0])
        for ss in sorted(bad):
            if ss in seen_cuts: continue
            seen_cuts.add(ss)
            model.AddBoolOr([Evar(u, v) for u, v in itertools.combinations(ss, 2) if not _is0(Evar(u, v))])
    return dict(task_id=task['id'], status=status_str, wall_s=round(time.monotonic() - t0, 3), models=models_found, i10_cuts=len(seen_cuts))

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--tasks-json', default='all_tasks.json')
    p.add_argument('--tasks', nargs='+', default=['D6-N9-B3-P002-T01', 'D6-N9-B3-P000-T01', 'D8-N8-B0-P000-T01'])
    p.add_argument('--seconds', type=float, default=45.0); p.add_argument('--workers', type=int, default=2)
    p.add_argument('--codeg', choices=['lazy', 'all'], default='lazy')
    a = p.parse_args()
    all_tasks = json.loads(Path(a.tasks_json).read_text())
    for tid in a.tasks:
        t = all_tasks[tid]
        v8_allowed = [(n, [x for x in feasible_v8(tuple(n), t['m'], t['d'], t['q'])[1] if t['tlo'] <= x <= t['thi']]) for n in t['profiles']]
        v8_allowed = [(n, xs) for n, xs in v8_allowed if xs]
        print(json.dumps(solve_cpsat(t, a.seconds, a.workers, a.codeg, v8_allowed)), flush=True)
