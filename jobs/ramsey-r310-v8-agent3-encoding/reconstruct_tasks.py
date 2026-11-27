#!/usr/bin/env python3
"""Reconstruct exact v6 profile_cert, branch_plan, v7 pilot/rollout tasks, and v8 group_filter locally."""
import hashlib, itertools, json, time
from functools import lru_cache
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

V = (6, 7, 8, 9)
E = {6: 118, 7: 104, 8: 95, 9: 86}
ET = {23: 35, 24: 40, 25: 46, 26: 52, 27: 61, 28: 68}
R = {1: 1, 2: 3, 3: 6, 4: 9, 5: 14, 6: 18, 7: 23, 8: 28, 9: 36}

@lru_cache(None)
def comps(n, k=4):
    if k == 1:
        return ((n,),)
    return tuple((i,) + s for i in range(n + 1) for s in comps(n - i, k - 1))

def dot(a, b):
    return sum(i * j for i, j in zip(a, b))

def profiles():
    for n in comps(40, 4):
        D = dot(n, (3, 2, 1, 0))
        if D % 2 or D > 38:
            continue
        m = 180 - D // 2
        L = [max(0, 9 * k + E[k] - m) for k in V]
        good = True
        for i, k in enumerate(V):
            if not n[i]:
                continue
            rem = k
            u = 0
            for j in range(4):
                z = min(rem, n[j] - (i == j))
                rem -= z
                u += z * (3 - j)
            if u < L[i]:
                good = False
                break
        if not good:
            continue
        if dot(n, L) > sum(n[i] * V[i] * (3 - i) for i in range(4)):
            continue
        if 2 * sum(n[i] * (3 - i) * L[i] for i in range(4)) > D * D:
            continue
        yield n, m

@lru_cache(None)
def types(n, m):
    out = []
    for i, k in enumerate(V):
        if not n[i]:
            continue
        h = 39 - k
        for a in comps(k, 4):
            if any(a[j] > n[j] - (j == i) for j in range(4)):
                continue
            sx = dot(a, V)
            cross = sx - k
            if not E[k] <= m - sx <= 4 * h:
                continue
            if cross < 2 * h - k * (10 - k):
                continue
            hn = [n[j] - a[j] - (i == j) for j in range(4)]
            caps = [min(k, l, k + l - 11) for l in V]
            if not h <= cross <= dot(hn, caps):
                continue
            if sum(hn[j] for j in range(4) if caps[j] == 1) > k * (10 - k):
                continue
            out.append((i, a))
    return out

P = list(itertools.combinations_with_replacement(range(4), 2))
D_pairs = list(itertools.combinations(range(4), 2))
NE = 4 + len(D_pairs)

def col(i, a):
    eq = [int(i == j) for j in range(4)] + [
        (a[j] if i == k else 0) - (a[k] if i == j else 0) for k, j in D_pairs
    ]
    ub = []
    for k, j in P:
        cap = V[k] + V[j] - 11
        if k == j:
            c = a[k] * (a[k] - 1)
            ed = a[k] if i == k else 0
        else:
            c = a[k] * a[j]
            ed = a[j] if i == k else 0
        ub.extend([-c - ed, c + cap * ed])
    return eq + ub

def rhs(n):
    b = list(n) + [0] * len(D_pairs)
    for k, j in P:
        v = n[k] * (n[k] - 1) if k == j else n[k] * n[j]
        b.extend([-v, (V[k] + V[j] - 11) * v])
    return b

def verify(n, m, y):
    ts = types(tuple(n), m)
    b = rhs(n)
    assert len(y) == len(b) and all(isinstance(v, int) for v in y) and min(y[NE:]) >= 0
    assert all(dot(col(i, a), y) >= 0 for i, a in ts)
    assert dot(y, b) < 0
    return True

def check_profile(n, m):
    ts = types(n, m)
    b = np.asarray(rhs(n), dtype=float)
    if not ts or any(n[i] and not any(j == i for j, a in ts) for i in range(4)):
        i = next(i for i in range(4) if n[i] and not any(j == i for j, a in ts))
        y = [0] * len(b)
        y[i] = -1
        verify(n, m, y)
        return y
    A = np.asarray([col(i, a) for i, a in ts], dtype=float).T
    res = linprog(np.zeros(len(ts)), A_eq=A[:NE], b_eq=b[:NE], A_ub=A[NE:], b_ub=b[NE:], bounds=(0, None), method='highs')
    if res.status == 0:
        return None
    if res.status != 2:
        raise RuntimeError(res.message)
    r = linprog(np.zeros(len(b)), A_ub=np.vstack([-A.T, b]), b_ub=np.r_[np.zeros(len(ts)), -1],
                bounds=[(None, None)] * NE + [(0, None)] * (len(b) - NE), method='highs')
    if not r.success:
        raise RuntimeError('dual fail ' + r.message)
    for scale in [1000, 1000000, 1000000000]:
        y = [round(scale * v) for v in r.x]
        for i in range(4):
            mn = min((dot(col(j, a), y) for j, a in ts if j == i), default=0)
            y[i] += max(0, -mn)
        if dot(y, b) < 0:
            verify(n, m, y)
            return y
    return None

def supports(n, m, d, q, strict=True):
    a = list(n)
    a[d - 6] -= 1
    a[q - 6] -= 1
    if min(a) < 0:
        return False
    ts = set(types(n, m)) if strict else None
    nt = 40 - d - q
    for x in comps(d - 1, 4):
        if any(x[i] > a[i] or (x[i] and V[i] < q) for i in range(4)):
            continue
        sx = dot(x, V)
        h0 = m - q - sx
        if not E[d] <= h0 <= 180 - 9 * d:
            continue
        ax = tuple(x[i] + (V[i] == q) for i in range(4))
        if strict and (d - 6, ax) not in ts:
            continue
        av = [a[i] - x[i] for i in range(4)]
        for y in comps(q - 1, 4):
            if any(y[i] > av[i] for i in range(4)):
                continue
            sy = dot(y, V)
            h1 = m - d - sy
            if not E[q] <= h1 <= 4 * (39 - q):
                continue
            ay = tuple(y[i] + (V[i] == d) for i in range(4))
            if strict and (q - 6, ay) not in ts:
                continue
            lo = max(0, ET[nt] - m + 1 + sx + sy)
            hi = min((d - 1) * (q - 1), sx + (d - 1) * (q - 12), sy + (q - 1) * (d - 12), 4 * nt - m + 1 + sx + sy)
            if strict:
                h0max = (7 * (39 - d) + d * (10 - d)) // 2
                h1max = (7 * (39 - q) + q * (10 - q)) // 2
                if h0 > h0max or h1 > h1max:
                    continue
            if lo <= hi:
                return True
    return False

def c2(n): return n * (n - 1) // 2
def min_pairs(total, n):
    q, r = divmod(total, n)
    return (n - r) * c2(q) + r * c2(q + 1)

@lru_cache(None)
def feasible_v8(n, m, d, q):
    nx, ny, nt = d - 1, q - 1, 40 - d - q
    avail = tuple(n[i] - (V[i] == d) - (V[i] == q) for i in range(4))
    if min(avail) < 0: return (), ()
    ts_d = [a for i, a in types(n, m) if i == d - 6]
    ts_q = [a for i, a in types(n, m) if i == q - 6]
    xx, yy = [], []
    for a in ts_d:
        x = tuple(a[i] - (V[i] == q) for i in range(4))
        if min(x) < 0 or any(x[i] > avail[i] or (x[i] and V[i] < q) for i in range(4)): continue
        sx = dot(x, V); h = m - q - sx
        if E[d] <= h <= min(180 - 9 * d, (7 * (39 - d) + d * (10 - d)) // 2): xx.append((x, sx))
    for a in ts_q:
        y = tuple(a[i] - (V[i] == d) for i in range(4))
        if min(y) < 0 or any(y[i] > avail[i] for i in range(4)): continue
        sy = dot(y, V); h = m - d - sy
        if E[q] <= h <= min(4 * (39 - q), (7 * (39 - q) + q * (10 - q)) // 2): yy.append((y, sy))
    old, new = set(), set()
    for x, sx in xx:
        ax = tuple(avail[i] - x[i] for i in range(4))
        for y, sy in yy:
            if any(y[i] > ax[i] for i in range(4)): continue
            z = tuple(ax[i] - y[i] for i in range(4))
            lo = max(0, ET[nt] - m + 1 + sx + sy)
            hi = min(nx * ny, sx + nx * (q - 12), sy + ny * (d - 12), 4 * nt - m + 1 + sx + sy)
            if lo > hi: continue
            old.update(range(lo, hi + 1))
            capx = sum(z[i] * min(nx, V[i] + d - 11) for i in range(4))
            capy = sum(z[i] * min(ny, V[i] + q - 11) for i in range(4))
            lo2 = max(lo, sx - nx - capx, sy - ny - capy)
            hi2 = min(hi, sx - nx - nt, sy - ny - nt)
            bx = (nx - 1) * sx - 12 * c2(nx)
            by = (ny - 1) * sy - 12 * c2(ny)
            for t in range(lo2, hi2 + 1):
                xt = sx - nx - t; yt = sy - ny - t
                if min_pairs(xt, nt) + min_pairs(t, ny) > bx: continue
                if min_pairs(yt, nt) + min_pairs(t, nx) > by: continue
                new.add(t)
    return tuple(sorted(old)), tuple(sorted(new))

def sha(x):
    return hashlib.sha256(json.dumps(x, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

def make_tasks(kept, bands, d, q, b, group_size, parts):
    band = next(x for x in bands if (x['d'], x['q'], x['band']) == (d, q, b))
    prof = sorted((m, list(n)) for n, m in kept if band['lo'] <= m <= band['hi'] and supports(n, m, d, q, True))
    hi = min((d - 1) * (q - 1), (d - 1) * (q - 3), (q - 1) * (d - 3))
    intervals = []
    for i in range(parts):
        lo = i * (hi + 1) // parts
        up = (i + 1) * (hi + 1) // parts - 1
        if lo <= up:
            intervals.append([lo, up])
    groups = []
    for m in sorted(set(m for m, n in prof)):
        ns = [n for mm, n in prof if mm == m]
        for j in range(0, len(ns), group_size):
            groups.append((m, ns[j:j + group_size]))
    tasks = []
    for g, (m, ns) in enumerate(groups):
        for i, (lo, up) in enumerate(intervals):
            task = dict(id=f'D{d}-N{q}-B{b}-P{g:03d}-T{i:02d}', d=d, q=q, band=b, m=m, profiles=ns, tlo=lo, thi=up)
            task['key'] = sha(task)
            tasks.append(task)
    return tasks

def main():
    t0 = time.monotonic()
    ps = list(profiles())
    assert len(ps) == 931
    keep = [nm for nm in ps if check_profile(*nm) is None]
    assert len(keep) == 543
    bands = []
    for d in (6, 7, 8):
        for q in V:
            old = [(n, m) for n, m in ps if supports(n, m, d, q, False)]
            new = [(n, m) for n, m in keep if supports(n, m, d, q, True)]
            ms = sorted(set(m for n, m in old))
            for k in range(4):
                b = ms[k * len(ms) // 4:(k + 1) * len(ms) // 4]
                ss = [(n, m) for n, m in new if m in b]
                bands.append(dict(d=d, q=q, band=k, lo=b[0], hi=b[-1], old_count=sum(m in b for n, m in old), new_count=len(ss), m_values=sorted({m for n, m in ss})))
    pilot_tasks = make_tasks(keep, bands, 6, 9, 3, 1, 8)
    rollout_tasks = []
    for b in bands:
        if b['new_count'] == 0 or (b['d'], b['q'], b['band']) == (6, 9, 3): continue
        part = 2 if b['new_count'] <= 70 else 1
        rollout_tasks.extend(make_tasks(keep, bands, b['d'], b['q'], b['band'], 10000, part))
    all_tasks = {t['id']: t for t in pilot_tasks + rollout_tasks}
    assert len(all_tasks) == 279
    Path('all_tasks.json').write_text(json.dumps(all_tasks, indent=2))
    print(f"Reconstructed {len(all_tasks)} tasks in {time.monotonic()-t0:.2f}s")

if __name__ == '__main__':
    main()
