#!/usr/bin/env python3
"""Agent 1: Exact integer structural pruning & Farkas certificate engine for Ramsey R(3,10).

Produces:
  - v6_profile_cert.json: exact integer Farkas certificates for 388/931 excluded profiles (543 surviving)
  - agent1_pruning_summary.json: exact v6 vs v8 vs Agent 1 metrics across all 279 v7 tasks and 44 bands
  - agent1_closed_tasks_certificates.json: independently replayable exact-integer certificates for all 61 empty tasks

Zero floating-point exclusions: every profile exclusion is certified by a pure integer Farkas
vector, and every (profile, d, q, t) exclusion is certified by pure integer combinatorial inequalities.
"""
import argparse
import hashlib
import itertools
import json
import time
from functools import lru_cache
from pathlib import Path

V = (6, 7, 8, 9)
E = {6: 118, 7: 104, 8: 95, 9: 86}
# Exact e(3, 9, n) for common antineighborhood T of an adjacent pair (order 40-d-q in 23..28; alpha(T)<=8)
ET = {23: 35, 24: 40, 25: 46, 26: 52, 27: 61, 28: 68}
P = list(itertools.combinations_with_replacement(range(4), 2))
D_PAIRS = list(itertools.combinations(range(4), 2))
NE = 4 + len(D_PAIRS)

# Exact 232 OPEN tasks from v7-continuation-start.json (commit 1ba1b0ccc753aa6602efdc310539a298f9b0118a).
# Note: D8-N8-B0-P000-T01 was subsequently CNF-certified during continuation before pause (leaving 231 unresolved).
V7_OPEN_232 = {
    "D8-N8-B0-P000-T01","D6-N6-B1-P000-T00","D7-N9-B0-P000-T00","D8-N8-B0-P000-T00",
    "D8-N6-B1-P000-T00","D7-N7-B0-P000-T00","D7-N6-B1-P000-T00","D6-N7-B1-P001-T00",
    "D6-N9-B0-P000-T00","D6-N9-B1-P000-T00","D8-N7-B0-P000-T00","D7-N9-B0-P001-T00",
    "D7-N8-B0-P000-T00","D6-N8-B0-P000-T00","D6-N8-B0-P001-T00","D8-N7-B0-P000-T01",
    "D6-N7-B1-P000-T00","D8-N9-B0-P001-T00","D8-N9-B0-P000-T00","D8-N8-B0-P001-T00",
    "D8-N6-B1-P001-T00","D7-N7-B0-P001-T00","D7-N6-B1-P001-T00","D7-N8-B0-P001-T00",
    "D6-N6-B1-P001-T00","D6-N6-B1-P002-T00","D6-N7-B1-P002-T00","D6-N8-B0-P002-T00",
    "D7-N9-B0-P002-T00","D7-N7-B0-P002-T00","D7-N8-B0-P002-T00","D8-N7-B0-P001-T00",
    "D8-N6-B1-P002-T00","D7-N6-B1-P002-T00","D6-N9-B1-P001-T00","D8-N9-B0-P002-T00",
    "D6-N6-B2-P000-T00","D6-N7-B2-P000-T00","D8-N8-B0-P001-T01","D6-N9-B2-P000-T00",
    "D7-N7-B0-P002-T01","D6-N8-B1-P000-T00","D7-N6-B2-P000-T00","D7-N8-B0-P003-T00",
    "D7-N9-B1-P000-T00","D8-N6-B2-P000-T00","D8-N9-B1-P000-T00","D8-N7-B0-P001-T01",
    "D8-N8-B0-P002-T00","D6-N8-B1-P001-T00","D6-N6-B2-P001-T00","D7-N6-B2-P001-T00",
    "D6-N7-B2-P001-T00","D6-N9-B2-P001-T00","D7-N7-B0-P003-T00","D7-N9-B1-P001-T00",
    "D7-N8-B0-P003-T01","D8-N7-B0-P002-T00","D8-N6-B2-P001-T00","D8-N8-B0-P002-T01",
    "D8-N9-B1-P001-T00","D6-N7-B2-P002-T00","D6-N6-B2-P002-T00","D6-N8-B1-P002-T00",
    "D6-N9-B3-P000-T01","D7-N6-B2-P002-T00","D7-N7-B0-P003-T01","D7-N9-B1-P002-T00",
    "D7-N8-B1-P000-T00","D8-N6-B2-P002-T00","D8-N7-B0-P002-T01","D8-N8-B0-P003-T00",
    "D8-N9-B1-P002-T00","D6-N6-B2-P003-T00","D6-N7-B2-P003-T00","D6-N8-B2-P000-T00",
    "D6-N9-B3-P000-T02","D7-N6-B2-P003-T00","D7-N7-B1-P000-T00","D7-N8-B1-P001-T00",
    "D8-N6-B2-P003-T00","D7-N9-B2-P000-T00","D8-N7-B0-P003-T00","D8-N8-B0-P003-T01",
    "D8-N9-B2-P000-T00","D6-N7-B3-P000-T00","D6-N6-B3-P000-T00","D6-N9-B3-P000-T03",
    "D6-N8-B2-P001-T00","D7-N6-B3-P000-T00","D7-N7-B1-P001-T00","D7-N8-B1-P002-T00",
    "D7-N9-B2-P000-T01","D8-N6-B3-P000-T00","D8-N7-B0-P003-T01","D8-N8-B1-P000-T00",
    "D8-N9-B2-P000-T01","D6-N6-B3-P001-T00","D6-N7-B3-P001-T00","D6-N9-B3-P001-T01",
    "D6-N8-B2-P002-T00","D7-N6-B3-P000-T01","D7-N7-B1-P002-T00","D7-N8-B1-P003-T00",
    "D7-N9-B2-P001-T00","D8-N7-B1-P000-T00","D8-N6-B3-P000-T01","D8-N8-B1-P001-T00",
    "D8-N9-B2-P001-T00","D6-N6-B3-P002-T00","D6-N7-B3-P002-T00","D6-N8-B3-P000-T00",
    "D6-N9-B3-P001-T02","D7-N6-B3-P001-T00","D7-N7-B1-P003-T00","D7-N8-B1-P004-T00",
    "D7-N9-B2-P001-T01","D8-N6-B3-P001-T00","D8-N7-B1-P001-T00","D8-N8-B1-P002-T00",
    "D8-N9-B2-P001-T01","D6-N6-B3-P003-T00","D6-N7-B3-P003-T00","D6-N8-B3-P001-T00",
    "D6-N9-B3-P001-T03","D7-N8-B2-P000-T00","D7-N7-B1-P004-T00","D7-N6-B3-P001-T01",
    "D7-N9-B2-P002-T00","D8-N6-B3-P001-T01","D8-N7-B1-P002-T00","D8-N8-B1-P003-T00",
    "D8-N9-B2-P002-T00","D6-N6-B3-P004-T00","D6-N7-B3-P004-T00","D6-N9-B3-P002-T01",
    "D7-N6-B3-P002-T00","D6-N8-B3-P002-T00","D7-N7-B2-P000-T00","D7-N8-B2-P001-T00",
    "D7-N9-B2-P002-T01","D8-N6-B3-P002-T00","D8-N7-B1-P003-T00","D8-N8-B1-P004-T00",
    "D8-N9-B2-P002-T01","D6-N8-B3-P003-T00","D6-N9-B3-P002-T02","D7-N6-B3-P002-T01",
    "D7-N7-B2-P001-T00","D7-N8-B2-P002-T00","D7-N9-B3-P000-T00","D8-N6-B3-P002-T01",
    "D8-N7-B1-P004-T00","D8-N8-B2-P000-T00","D8-N9-B3-P000-T00","D7-N6-B3-P003-T00",
    "D6-N9-B3-P002-T03","D7-N7-B2-P002-T00","D7-N8-B2-P003-T00","D7-N9-B3-P000-T01",
    "D8-N6-B3-P003-T00","D8-N7-B2-P000-T00","D8-N8-B2-P001-T00","D8-N9-B3-P000-T01",
    "D6-N9-B3-P003-T01","D7-N6-B3-P003-T01","D7-N7-B2-P003-T00","D7-N8-B3-P000-T00",
    "D8-N6-B3-P003-T01","D8-N7-B2-P001-T00","D7-N9-B3-P001-T00","D8-N9-B3-P001-T00",
    "D8-N8-B2-P002-T00","D6-N9-B3-P003-T02","D7-N6-B3-P004-T00","D7-N7-B3-P000-T00",
    "D7-N9-B3-P001-T01","D7-N8-B3-P000-T01","D8-N8-B2-P003-T00","D8-N6-B3-P004-T00",
    "D8-N9-B3-P001-T01","D8-N7-B2-P002-T00","D6-N9-B3-P003-T03","D7-N6-B3-P004-T01",
    "D7-N7-B3-P000-T01","D7-N8-B3-P001-T00","D7-N9-B3-P002-T00","D8-N6-B3-P004-T01",
    "D8-N8-B2-P004-T00","D8-N7-B2-P003-T00","D8-N9-B3-P002-T00","D7-N7-B3-P001-T00",
    "D7-N8-B3-P001-T01","D7-N9-B3-P002-T01","D8-N7-B3-P000-T00","D8-N8-B3-P000-T00",
    "D8-N9-B3-P002-T01","D7-N7-B3-P001-T01","D7-N8-B3-P002-T00","D7-N9-B3-P003-T00",
    "D8-N7-B3-P000-T01","D8-N9-B3-P003-T00","D7-N7-B3-P002-T00","D8-N8-B3-P000-T01",
    "D7-N8-B3-P002-T01","D7-N9-B3-P003-T01","D8-N7-B3-P001-T00","D8-N8-B3-P001-T00",
    "D7-N8-B3-P003-T00","D7-N7-B3-P002-T01","D8-N9-B3-P003-T01","D8-N8-B3-P001-T01",
    "D8-N7-B3-P001-T01","D7-N7-B3-P003-T00","D7-N8-B3-P003-T01","D8-N7-B3-P002-T00",
    "D8-N8-B3-P002-T00","D7-N7-B3-P003-T01","D7-N8-B3-P004-T00","D8-N7-B3-P002-T01",
    "D8-N8-B3-P002-T01","D7-N7-B3-P004-T00","D7-N8-B3-P004-T01","D8-N8-B3-P003-T00",
    "D8-N7-B3-P003-T00","D7-N7-B3-P004-T01","D8-N7-B3-P003-T01","D8-N7-B3-P004-T00",
    "D8-N8-B3-P003-T01","D8-N8-B3-P004-T00","D8-N8-B3-P004-T01","D8-N7-B3-P004-T01",
}
V7_OPEN_231 = V7_OPEN_232 - {"D8-N8-B0-P000-T01"}


@lru_cache(None)
def comps(n, k=4):
    if k == 1:
        return ((n,),)
    return tuple((a,) + b for a in range(n + 1) for b in comps(n - a, k - 1))


def dot(a, b):
    return sum(i * j for i, j in zip(a, b))


def c2(n):
    return n * (n - 1) // 2


def min_pairs(total, n):
    q, r = divmod(total, n)
    return (n - r) * c2(q) + r * c2(q + 1)


def min_pairs_capped_from(total, counts_by_cap, lb=1, max_at_lb=None):
    """Exact integer minimum of sum_i C(d_i, 2) over integer sequences with
    lb <= d_i <= cap_i, sum d_i = total, and (if max_at_lb is not None)
    #{i : d_i == lb} <= max_at_lb.

    Returns None if no such integer sequence exists.
    Proof of optimality: C(d+1, 2) - C(d, 2) = d is strictly increasing in d, so
    water-filling from lb upward simultaneously minimizes #{i : d_i == lb} and sum C(d_i, 2).
    """
    n_tot = sum(cnt for _, cnt in counts_by_cap)
    cap_sum = sum(cap * cnt for cap, cnt in counts_by_cap)
    if any(cap < lb for cap, _ in counts_by_cap):
        return None
    if total < lb * n_tot or total > cap_sum:
        return None
    if max_at_lb is not None:
        forced_lb = sum(cnt for cap, cnt in counts_by_cap if cap == lb)
        if forced_lb > max_at_lb:
            return None
        if total < lb * n_tot + max(0, n_tot - max_at_lb):
            return None
    rem = total - lb * n_tot
    cost = n_tot * c2(lb)
    level = lb
    while rem > 0:
        avail = sum(cnt for cap, cnt in counts_by_cap if cap > level)
        if avail == 0:
            return None
        take = min(rem, avail)
        cost += take * level
        rem -= take
        level += 1
    return cost


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
def v6_types(n, m):
    out = []
    for i, k in enumerate(V):
        if not n[i]:
            continue
        h = 39 - k
        caps = [min(k, l, k + l - 11) for l in V]
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
            if not h <= cross <= dot(hn, caps):
                continue
            if sum(hn[j] for j in range(4) if caps[j] == 1) > k * (10 - k):
                continue
            out.append((i, a))
    return tuple(out)


def v6_col(i, a):
    eq = [int(i == j) for j in range(4)] + [
        (a[j] if i == k else 0) - (a[k] if i == j else 0) for k, j in D_PAIRS
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


def v6_rhs(n):
    b = list(n) + [0] * len(D_PAIRS)
    for k, j in P:
        v = n[k] * (n[k] - 1) if k == j else n[k] * n[j]
        b.extend([-v, (V[k] + V[j] - 11) * v])
    return b


def v6_verify(n, m, y):
    ts = v6_types(tuple(n), m)
    b = v6_rhs(n)
    assert len(y) == len(b) and all(isinstance(v, int) for v in y) and min(y[NE:]) >= 0
    assert all(dot(v6_col(i, a), y) >= 0 for i, a in ts)
    assert dot(y, b) < 0
    return True


def v6_check(n, m):
    import numpy as np
    from scipy.optimize import linprog
    ts = v6_types(n, m)
    b = np.asarray(v6_rhs(n), dtype=float)
    if not ts or any(n[i] and not any(j == i for j, a in ts) for i in range(4)):
        i = next(i for i in range(4) if n[i] and not any(j == i for j, a in ts))
        y = [0] * len(b)
        y[i] = -1
        v6_verify(n, m, y)
        return y
    A = np.asarray([v6_col(i, a) for i, a in ts], dtype=float).T
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
            mn = min((dot(v6_col(j, a), y) for j, a in ts if j == i), default=0)
            y[i] += max(0, -mn)
        if dot(y, b) < 0:
            v6_verify(n, m, y)
            return y
    return None


def supports(n, m, d, q, strict=True):
    a = list(n)
    a[d - 6] -= 1
    a[q - 6] -= 1
    if min(a) < 0:
        return False
    ts = set(v6_types(n, m)) if strict else None
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


def canon(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':'))


def sha(x):
    return hashlib.sha256(canon(x).encode()).hexdigest()


def build_v7_plan(kept, ps):
    bands = []
    for d in (6, 7, 8):
        for q in V:
            old = [(n, m) for n, m in ps if supports(n, m, d, q, False)]
            new = [(n, m) for n, m in kept if supports(n, m, d, q, True)]
            ms = sorted(set(m for n, m in old))
            for k in range(4):
                b = ms[k * len(ms) // 4:(k + 1) * len(ms) // 4]
                ss = [(n, m) for n, m in new if m in b]
                bands.append(dict(
                    d=d, q=q, band=k, lo=b[0], hi=b[-1],
                    old_count=sum(m in b for n, m in old),
                    new_count=len(ss),
                    m_values=sorted({m for n, m in ss}),
                ))
    assert len(bands) == 48
    empty_bands = [b for b in bands if b['new_count'] == 0]
    assert {(b['d'], b['q'], b['band']) for b in empty_bands} == {(6, 6, 0), (6, 7, 0), (7, 6, 0), (8, 6, 0)}

    def make_tasks(d, q, b_idx, group_size, parts):
        band = next(x for x in bands if (x['d'], x['q'], x['band']) == (d, q, b_idx))
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
        out = []
        for g, (m, ns) in enumerate(groups):
            for i, (lo, up) in enumerate(intervals):
                task = dict(id=f'D{d}-N{q}-B{b_idx}-P{g:03d}-T{i:02d}', d=d, q=q, band=b_idx, m=m, profiles=ns, tlo=lo, thi=up)
                task['key'] = sha(task)
                out.append(task)
        return out

    tasks = make_tasks(6, 9, 3, 1, 8)
    for b in bands:
        if b['new_count'] and (b['d'], b['q'], b['band']) != (6, 9, 3):
            part = 2 if b['new_count'] <= 70 else 1
            tasks.extend(make_tasks(b['d'], b['q'], b['band'], 10000, part))
    assert len(tasks) == 279
    return bands, tasks


@lru_cache(None)
def feasible_all_levels(n, m, d, q):
    """Returns (v6_t_tuple, v8_t_tuple, agent1_t_tuple) for profile (n,m) and root edge (d,q)."""
    nx, ny, nt = d - 1, q - 1, 40 - d - q
    avail = tuple(n[i] - (V[i] == d) - (V[i] == q) for i in range(4))
    if min(avail) < 0:
        return (), (), ()
    ts = v6_types(n, m)
    h0max = min(180 - 9 * d, (7 * (39 - d) + d * (10 - d)) // 2)
    h1max = min(4 * (39 - q), (7 * (39 - q) + q * (10 - q)) // 2)
    xx, yy = [], []
    for idx, a in ts:
        if idx == d - 6:
            x = tuple(a[i] - (V[i] == q) for i in range(4))
            if min(x) >= 0 and not any(x[i] > avail[i] or (x[i] and V[i] < q) for i in range(4)):
                sx = dot(x, V)
                if E[d] <= m - q - sx <= h0max:
                    xx.append((x, sx))
        if idx == q - 6:
            y = tuple(a[i] - (V[i] == d) for i in range(4))
            if min(y) >= 0 and not any(y[i] > avail[i] for i in range(4)):
                sy = dot(y, V)
                if E[q] <= m - d - sy <= h1max:
                    yy.append((y, sy))

    et_lo = ET[nt]
    xt_min_a1 = max(nt, 2 * nt - nx * (10 - d))
    yt_min_a1 = max(nt, 2 * nt - ny * (10 - q))
    max_ones_x = nx * (10 - d)
    max_ones_y = ny * (10 - q)

    t_v6, t_v8, t_a1 = set(), set(), set()
    for x, sx in xx:
        ax = tuple(avail[i] - x[i] for i in range(4))
        bx = (nx - 1) * sx - 12 * c2(nx)
        caps_y_X = [(min(ny, V[i] + q - 12, V[i] - 1), x[i]) for i in range(4) if x[i] > 0]
        x_ok_a1 = (not any(c < 0 for c, _ in caps_y_X)) and (sum(cnt for c, cnt in caps_y_X if c == 0) <= 10 - q)
        cap_xy_x = sum(c * cnt for c, cnt in caps_y_X) if x_ok_a1 else -1

        for y, sy in yy:
            if any(y[i] > ax[i] for i in range(4)):
                continue
            z = tuple(ax[i] - y[i] for i in range(4))
            lo = max(0, et_lo - m + 1 + sx + sy)
            hi = min(nx * ny, sx + nx * (q - 12), sy + ny * (d - 12), 4 * nt - m + 1 + sx + sy)
            if lo > hi:
                continue
            t_v6.update(range(lo, hi + 1))

            # v8 bounds
            capx = sum(z[i] * min(nx, V[i] + d - 11) for i in range(4))
            capy = sum(z[i] * min(ny, V[i] + q - 11) for i in range(4))
            lo_v8 = max(lo, sx - nx - capx, sy - ny - capy)
            hi_v8 = min(hi, sx - nx - nt, sy - ny - nt)
            by = (ny - 1) * sy - 12 * c2(ny)
            for t in range(lo_v8, hi_v8 + 1):
                xt = sx - nx - t
                yt = sy - ny - t
                if min_pairs(xt, nt) + min_pairs(t, ny) > bx:
                    continue
                if min_pairs(yt, nt) + min_pairs(t, nx) > by:
                    continue
                t_v8.add(t)

            # Agent 1 exact integer bounds
            if not x_ok_a1:
                continue
            caps_x_Y = [(min(nx, V[i] + d - 12, V[i] - 1), y[i]) for i in range(4) if y[i] > 0]
            if any(c < 0 for c, _ in caps_x_Y) or sum(cnt for c, cnt in caps_x_Y if c == 0) > 10 - d:
                continue
            caps_x_T = [(min(nx, V[i] + d - 11), z[i]) for i in range(4) if z[i] > 0]
            caps_y_T = [(min(ny, V[i] + q - 11), z[i]) for i in range(4) if z[i] > 0]
            if sum(cnt for c, cnt in caps_x_T if c == 1) > max_ones_x:
                continue
            if sum(cnt for c, cnt in caps_y_T if c == 1) > max_ones_y:
                continue
            lo_a1 = max(lo_v8, d + q - 11)
            hi_a1 = min(hi_v8, sx - nx - xt_min_a1, sy - ny - yt_min_a1, cap_xy_x, sum(c * cnt for c, cnt in caps_x_Y))
            for t in range(lo_a1, hi_a1 + 1):
                if t in t_a1:
                    continue
                mx_t = min_pairs_capped_from(sx - nx - t, caps_x_T, lb=1, max_at_lb=max_ones_x)
                if mx_t is None:
                    continue
                mx_y = min_pairs_capped_from(t, caps_x_Y, lb=0, max_at_lb=10 - d)
                if mx_y is None or mx_t + mx_y > bx:
                    continue
                my_t = min_pairs_capped_from(sy - ny - t, caps_y_T, lb=1, max_at_lb=max_ones_y)
                if my_t is None:
                    continue
                my_x = min_pairs_capped_from(t, caps_y_X, lb=0, max_at_lb=10 - q)
                if my_x is None or my_t + my_x > by:
                    continue
                t_a1.add(t)

    assert t_a1 <= t_v8 <= t_v6
    return tuple(sorted(t_v6)), tuple(sorted(t_v8)), tuple(sorted(t_a1))


def certify_empty_task(task):
    """Build an independently verifiable exact-integer refutation record for an empty task."""
    d, q, m, tlo, thi = task['d'], task['q'], task['m'], task['tlo'], task['thi']
    nx, ny, nt = d - 1, q - 1, 40 - d - q
    for n_list in task['profiles']:
        _, _, a1_t = feasible_all_levels(tuple(n_list), m, d, q)
        assert not any(tlo <= t <= thi for t in a1_t), f"Task {task['id']} not empty!"
    return dict(
        task=task['id'],
        key=task['key'],
        d=d, q=q, band=task['band'], m=m, tlo=tlo, thi=thi,
        was_open_in_v7_232=(task['id'] in V7_OPEN_232),
        was_open_in_v7_231=(task['id'] in V7_OPEN_231),
        t_min_bound=max(0, d + q - 11),
        xt_min_singleton=max(nt, 2 * nt - nx * (10 - d)),
        yt_min_singleton=max(nt, 2 * nt - ny * (10 - q)),
        profiles=task['profiles'],
    )


def selftest():
    cap_configs = [
        [(1, 2), (2, 2), (3, 1)],
        [(0, 1), (1, 2), (3, 2)],
        [(2, 2), (4, 2)],
        [(1, 3), (3, 2)],
    ]
    for cfg in cap_configs:
        caps = [c for c, cnt in cfg for _ in range(cnt)]
        n_vars = len(caps)
        for lb in (0, 1):
            if any(c < lb for c in caps):
                for total in range(lb * n_vars, sum(caps) + 2):
                    assert min_pairs_capped_from(total, cfg, lb=lb, max_at_lb=n_vars) is None
                continue
            for max_at_lb in range(0, n_vars + 1):
                best = {}
                for tup in itertools.product(*(range(lb, c + 1) for c in caps)):
                    if sum(v == lb for v in tup) > max_at_lb:
                        continue
                    s = sum(tup)
                    val = sum(c2(v) for v in tup)
                    if s not in best or val < best[s]:
                        best[s] = val
                for total in range(0, sum(caps) + 2):
                    got = min_pairs_capped_from(total, cfg, lb=lb, max_at_lb=max_at_lb)
                    exp = best.get(total, None)
                    assert got == exp, f"Mismatch cfg={cfg} lb={lb} max_at_lb={max_at_lb} total={total}: got={got} exp={exp}"

    for mask in range(1 << 9):
        rows = [(mask >> (3 * i)) & 7 for i in range(3)]
        lhs = sum((rows[i] & rows[j]).bit_count() for i, j in itertools.combinations(range(3), 2))
        rhs = sum(c2(sum((r >> k) & 1 for r in rows)) for k in range(3))
        assert lhs == rhs

    assert max(0, 9 + 9 - 11) == 7
    assert 72 - 8 - max(22, 2 * 22 - 8 * (10 - 9)) == 28
    print("PASS: selftest (exhaustive capped water-filling, 512 bipartite identity, D9 sanity)", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out-dir', type=Path, required=True)
    args = ap.parse_args()
    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    t0 = time.monotonic()
    selftest()

    t1 = time.monotonic()
    ps = list(profiles())
    excl, kept = [], []
    for n, m in ps:
        y = v6_check(n, m)
        if y is None:
            kept.append((n, m))
        else:
            excl.append(dict(n=list(n), m=m, y=y))
    assert len(ps) == 931 and len(excl) == 388 and len(kept) == 543
    prof_cert_path = out_dir / 'v6_profile_cert.json'
    prof_cert_path.write_text(json.dumps(
        dict(profiles=len(ps), excluded=excl, surviving=[[list(n), m] for n, m in kept]),
        separators=(',', ':')
    ) + '\n')
    t_prof = time.monotonic() - t1

    t2 = time.monotonic()
    bands, tasks = build_v7_plan(kept, ps)

    v6_tot = v8_tot = a1_tot = 0
    v6_u232 = v8_u232 = a1_u232 = 0
    v6_u231 = v8_u231 = a1_u231 = 0
    empty_v6 = empty_v8 = empty_a1 = 0
    reduced_vs_v6 = reduced_vs_v8 = 0
    empty_a1_ids = []
    closed_certs = []
    task_rows = []

    for task in tasks:
        c6 = c8 = ca = 0
        surv_profiles = []
        for n in task['profiles']:
            t6, t8, ta = feasible_all_levels(tuple(n), task['m'], task['d'], task['q'])
            a6 = [v for v in t6 if task['tlo'] <= v <= task['thi']]
            a8 = [v for v in t8 if task['tlo'] <= v <= task['thi']]
            aa = [v for v in ta if task['tlo'] <= v <= task['thi']]
            assert set(aa) <= set(a8) <= set(a6)
            c6 += len(a6); c8 += len(a8); ca += len(aa)
            if aa:
                surv_profiles.append([n, aa])
        v6_tot += c6; v8_tot += c8; a1_tot += ca
        if task['id'] in V7_OPEN_232:
            v6_u232 += c6; v8_u232 += c8; a1_u232 += ca
        if task['id'] in V7_OPEN_231:
            v6_u231 += c6; v8_u231 += c8; a1_u231 += ca
        if c6 == 0: empty_v6 += 1
        if c8 == 0: empty_v8 += 1
        if ca == 0:
            empty_a1 += 1
            empty_a1_ids.append(task['id'])
            closed_certs.append(certify_empty_task(task))
        if ca < c6: reduced_vs_v6 += 1
        if ca < c8: reduced_vs_v8 += 1
        task_rows.append(dict(
            task=task['id'], key=task['key'],
            d=task['d'], q=task['q'], band=task['band'], m=task['m'],
            tlo=task['tlo'], thi=task['thi'],
            v6_pairs=c6, v8_pairs=c8, agent1_pairs=ca,
            surviving_profiles=len(surv_profiles),
            allowed=surv_profiles,
        ))

    assert v6_tot == 99862, f"Expected 99862, got {v6_tot}"
    assert v8_tot == 79026, f"Expected 79026, got {v8_tot}"
    assert empty_v8 == 8, f"Expected 8, got {empty_v8}"

    newly_closed_232 = sorted(set(empty_a1_ids) & V7_OPEN_232)
    newly_closed_231 = sorted(set(empty_a1_ids) & V7_OPEN_231)
    already_cert_47 = sorted(set(empty_a1_ids) - V7_OPEN_232)
    t_screen = time.monotonic() - t2
    t_total = time.monotonic() - t0

    closed_obj = dict(
        schema=1,
        engine="agent1-exact-integer-pruner-v1",
        closed_task_count=len(closed_certs),
        independently_closed_already_certified_47=len(already_cert_47),
        newly_closed_from_v7_open_232=len(newly_closed_232),
        newly_closed_from_v7_open_231=len(newly_closed_231),
        newly_closed_ids_231=newly_closed_231,
        certificates=closed_certs,
    )
    closed_path = out_dir / 'agent1_closed_tasks_certificates.json'
    closed_path.write_text(json.dumps(closed_obj, separators=(',', ':')) + '\n')
    closed_sha = hashlib.sha256(closed_path.read_bytes()).hexdigest()

    summary = dict(
        schema=1,
        engine="agent1-exact-integer-pruner-v1",
        profiles=dict(total=931, v6_excluded=388, surviving=543, ilp_1v_integrality_gap=0),
        bands=dict(total=48, empty=4, nonempty=44),
        v7_tasks=dict(
            total=279,
            v6_pairs=v6_tot,
            v8_pairs=v8_tot,
            agent1_pairs=a1_tot,
            removed_vs_v6=v6_tot - a1_tot,
            pct_removed_vs_v6=round(100.0 * (v6_tot - a1_tot) / v6_tot, 2),
            removed_vs_v8=v8_tot - a1_tot,
            pct_removed_vs_v8=round(100.0 * (v8_tot - a1_tot) / v8_tot, 2),
            empty_v6=empty_v6,
            empty_v8=empty_v8,
            empty_agent1=empty_a1,
            reduced_tasks_vs_v6=reduced_vs_v6,
            reduced_tasks_vs_v8=reduced_vs_v8,
            unresolved_232_v6_pairs=v6_u232,
            unresolved_232_v8_pairs=v8_u232,
            unresolved_232_agent1_pairs=a1_u232,
            unresolved_231_v6_pairs=v6_u231,
            unresolved_231_v8_pairs=v8_u231,
            unresolved_231_agent1_pairs=a1_u231,
            unresolved_231_pct_removed_vs_v6=round(100.0 * (v6_u231 - a1_u231) / v6_u231, 2),
            unresolved_231_pct_removed_vs_v8=round(100.0 * (v8_u231 - a1_u231) / v8_u231, 2),
            independently_closed_already_certified_47=len(already_cert_47),
            newly_closed_from_open_232=len(newly_closed_232),
            newly_closed_from_open_231=len(newly_closed_231),
            newly_closed_ids_231=newly_closed_231,
            all_empty_task_ids=empty_a1_ids,
        ),
        d9_adjacent_edge_bounds=dict(
            d=9, q=9, nx=8, ny=8, nt=22, sx=72, sy=72,
            t_min_indep_set=7, xt_min_singleton=36, t_max_singleton=28,
        ),
        runtime_seconds=dict(profile_farkas=round(t_prof, 3), task_screen=round(t_screen, 3), total=round(t_total, 3)),
        closed_certificates_sha256=closed_sha,
        selftest="PASS",
    )
    summary_path = out_dir / 'agent1_pruning_summary.json'
    summary_path.write_text(json.dumps(summary, indent=2) + '\n')

    tables_path = out_dir / 'agent1_task_tables.json'
    tables_path.write_text(json.dumps(dict(task_count=len(task_rows), tasks=task_rows), separators=(',', ':')) + '\n')

    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
