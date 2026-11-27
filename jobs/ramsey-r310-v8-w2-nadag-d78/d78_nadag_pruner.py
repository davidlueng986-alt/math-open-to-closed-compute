#!/usr/bin/env python3
"""Unified Non-Adjacent-Root DAG (Tier-2 D78) Exact Pure-Integer Pruner & Verifier.

Covers 100% of all non-9-regular saturated (3,10;40)-graphs with delta(G) in {7, 8}
(i.e. n_6 = 0, n_7 + n_8 > 0; all 209 surviving D78 degree profiles from the 931 -> 543
v6 Farkas partition).

Mathematical architecture:
  - Agent 4 Tier-2 NA-DAG (commit 1f4691d2):
      T*(W) = max_{x !~ y} |T(x, y)| in {24, 25, 26, 27} (T* <= 23 Farkas-refuted for all 542 D678).
      Lex-max tie-breaking on (min(du, dv), max(du, dv)) in order
      (9,9) > (8,9) > (8,8) > (7,9) > (7,8) > (7,7) yields 23 algebraic branches
      (22 nonempty + 1 Farkas-empty branch (T*=24, du=7, dv=8, c=1)).
  - Agent 1 Exact Pure-Integer Inequalities (commit 89faecc9) adapted to NA-DAG:
      1. Konig / saturation + singleton lower bound on t = e(X, Y):
           deg_Y(x) >= 1 for all x in X, deg_X(y) >= 1 for all y in Y,
           t >= max(n_X, n_Y, 2*n_Y - n_X*(10 - du), 2*n_X - n_Y*(10 - dv)).
      2. Rooted singleton caps on A = S u X and B = S u Y (both T alone and joint T u Y / T u X):
           n_{1,A}(T) + n_{1,X}(Y) <= du*(10 - du) - 1_{c==1},
           n_{1,B}(T) + n_{1,Y}(X) <= dv*(10 - dv) - 1_{c==1}.
      3. Tie-broken global non-edge codegree caps on Y, X, and T (with deg_T(w) >= n_T - 23):
           1 <= deg_X(y) <= min(n_X, cap(du, d_y), d_y - 1),
           1 <= deg_Y(x) <= min(n_Y, cap(dv, d_x), d_x - 1),
           1 <= deg_A(w) <= min(du, cap(du, d_w), d_w - (n_T - 23)),
           1 <= deg_B(w) <= min(dv, cap(dv, d_w), d_w - (n_T - 23)),
           0 <= deg_S(w) <= min(c, d_w - (n_T - 23)).
      4. Exact water-filling degree-capped & singleton-capped convexity on
         (A -> T), (A -> Y), (B -> T), (B -> X), and (S -> T).

Zero floating-point exclusions: every profile/branch exclusion is certified by either
a pure-integer Farkas vector (dot(y, b) < 0, A^T y >= 0, y[NE:] >= 0) or an exact
pure-integer combinatorial refutation independently replayable using Python stdlib only.
"""
import argparse
import hashlib
import itertools
import json
import time
from functools import lru_cache
from pathlib import Path

V = (6, 7, 8, 9)
E9 = {6: 118, 7: 104, 8: 95, 9: 86}
# Exact e(3, 8, n) from Goedgebeur & Radziszowski (2013)
E8 = {21: 35, 22: 42, 23: 49, 24: 56, 25: 65, 26: 73, 27: 85}
E8MAX = {23: 80, 24: 84, 25: 87, 26: 91, 27: 94}

P_PAIRS = list(itertools.combinations_with_replacement(range(4), 2))
D_PAIRS = list(itertools.combinations(range(4), 2))
NE = 4 + len(D_PAIRS)

D78_DEG_PAIRS = ((9, 9), (8, 9), (8, 8), (7, 9), (7, 8), (7, 7))
TIER2_TSTAR_VALUES = (27, 26, 25, 24)


@lru_cache(None)
def comps(n: int, k: int = 4):
    if k == 1:
        return ((n,),)
    return tuple((a,) + b for a in range(n + 1) for b in comps(n - a, k - 1))


def dot(a, b) -> int:
    return sum(x * y for x, y in zip(a, b))


def c2(n: int) -> int:
    return n * (n - 1) // 2


def min_pairs(total: int, n: int) -> int:
    if n == 0:
        return 0 if total == 0 else 10**9
    q, r = divmod(total, n)
    return (n - r) * c2(q) + r * c2(q + 1)


def min_pairs_capped_from(total: int, counts_by_cap, lb: int = 1, max_at_lb=None):
    """Exact integer minimum of sum_i C(d_i, 2) over integer sequences with
    lb <= d_i <= cap_i, sum d_i = total, and (if max_at_lb is not None)
    #{i : d_i == lb} <= max_at_lb.

    Returns None if no such integer sequence exists.
    Proof: C(d+1, 2) - C(d, 2) = d is strictly increasing in d, so water-filling
    from lb upward simultaneously minimizes #{i : d_i == lb} and sum C(d_i, 2).
    """
    n_tot = 0
    cap_sum = 0
    forced_lb = 0
    for cap, cnt in counts_by_cap:
        if cnt == 0:
            continue
        if cap < lb:
            return None
        n_tot += cnt
        cap_sum += cap * cnt
        if cap == lb:
            forced_lb += cnt
    if total < lb * n_tot or total > cap_sum:
        return None
    if max_at_lb is not None:
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
        take = rem if rem < avail else avail
        cost += take * level
        rem -= take
        level += 1
    return cost


def initial_profiles():
    """Exact 931 initial degree profiles for saturated (3,10;40)-graphs."""
    out = []
    for n in comps(40, 4):
        D = dot(n, (3, 2, 1, 0))
        if D % 2 or D > 38:
            continue
        m = 180 - D // 2
        L = [max(0, 9 * k + E9[k] - m) for k in V]
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
        out.append((n, m))
    return out


def cap_matrix_uniform(Tmax: int):
    shift = 38 - Tmax
    return tuple(
        tuple(min(V[i], V[j], V[i] + V[j] - shift) for j in range(4))
        for i in range(4)
    )


def cap_matrix_tiebroken(Tstar: int, du: int, dv: int):
    shift = 38 - Tstar
    rows = []
    for i in range(4):
        row = []
        for j in range(4):
            a, b = min(V[i], V[j]), max(V[i], V[j])
            sh = (shift + 1) if (a > du or (a == du and b > dv)) else shift
            row.append(min(V[i], V[j], V[i] + V[j] - sh))
        rows.append(tuple(row))
    return tuple(rows)


def all_tier2_algebraic_branches():
    """All 23 algebraically valid Tier-2 D78 (T*, du, dv, c) branches."""
    out = []
    for Tstar in TIER2_TSTAR_VALUES:
        shift = 38 - Tstar
        for du, dv in D78_DEG_PAIRS:
            c = du + dv - shift
            if 1 <= c <= du:
                out.append({
                    'branch_id': f'D78-T{Tstar}-D{du}{dv}-C{c}',
                    'Tstar': Tstar,
                    'du': du,
                    'dv': dv,
                    'c': c,
                    'nx': du - c,
                    'ny': dv - c,
                    'nT': Tstar,
                })
    assert len(out) == 23
    return out


@lru_cache(None)
def local_types(n, m: int, cap):
    out = []
    for i, k in enumerate(V):
        if not n[i]:
            continue
        h = 39 - k
        eH_hi = min(4 * h, (7 * h + k * (10 - k)) // 2)
        for a in comps(k, 4):
            if any(a[j] > n[j] - (j == i) for j in range(4)):
                continue
            sx = dot(a, V)
            cross = sx - k
            eH = m - sx
            if not E9[k] <= eH <= eH_hi:
                continue
            if cross < 2 * h - k * (10 - k):
                continue
            hn = [n[j] - a[j] - (i == j) for j in range(4)]
            if any(hn[j] > 0 and cap[i][j] < 1 for j in range(4)):
                continue
            if not h <= cross <= sum(hn[j] * cap[i][j] for j in range(4)):
                continue
            if sum(hn[j] for j in range(4) if cap[i][j] == 1) > k * (10 - k):
                continue
            out.append((i, a))
    return tuple(out)


def lp_col(i: int, a, cap):
    eq = [int(i == j) for j in range(4)] + [
        (a[j] if i == k else 0) - (a[k] if i == j else 0) for k, j in D_PAIRS
    ]
    ub = []
    for k, j in P_PAIRS:
        c_cap = cap[k][j]
        if k == j:
            cc = a[k] * (a[k] - 1)
            ed = a[k] if i == k else 0
        else:
            cc = a[k] * a[j]
            ed = a[j] if i == k else 0
        ub.extend([-cc - ed, cc + c_cap * ed])
    return eq + ub


def lp_rhs(n, cap):
    b = list(n) + [0] * len(D_PAIRS)
    for k, j in P_PAIRS:
        c_cap = cap[k][j]
        v = n[k] * (n[k] - 1) if k == j else n[k] * n[j]
        b.extend([-v, c_cap * v])
    return b


def verify_farkas(n, m: int, cap, y) -> bool:
    """Pure-integer Farkas verifier (zero floating-point trust)."""
    ts = local_types(tuple(n), m, cap)
    b = lp_rhs(n, cap)
    assert len(y) == len(b)
    assert all(type(v) is int for v in y)
    assert min(y[NE:]) >= 0
    assert all(dot(lp_col(i, a, cap), y) >= 0 for i, a in ts)
    assert dot(y, b) < 0
    return True


def check_lp_and_certify(n, m: int, cap):
    """Returns pure-integer Farkas vector y if infeasible, else None."""
    ts = local_types(n, m, cap)
    b = lp_rhs(n, cap)
    if not ts or any(n[i] and not any(j == i for j, a in ts) for i in range(4)):
        i = next(i for i in range(4) if n[i] and not any(j == i for j, a in ts))
        y = [0] * len(b)
        y[i] = -1
        verify_farkas(n, m, cap, y)
        return y
    import numpy as np
    from scipy.optimize import linprog

    A = np.asarray([lp_col(i, a, cap) for i, a in ts], dtype=float).T
    bf = np.asarray(b, dtype=float)
    res = linprog(
        np.zeros(len(ts)),
        A_eq=A[:NE], b_eq=bf[:NE],
        A_ub=A[NE:], b_ub=bf[NE:],
        bounds=(0, None), method='highs',
    )
    if res.status == 0:
        return None
    if res.status != 2:
        raise RuntimeError(f'Unexpected HiGHS status {res.status}: {res.message}')
    r = linprog(
        np.zeros(len(b)),
        A_ub=np.vstack([-A.T, bf]),
        b_ub=np.r_[np.zeros(len(ts)), -1.0],
        bounds=[(None, None)] * NE + [(0, None)] * (len(b) - NE),
        method='highs',
    )
    if not r.success:
        raise RuntimeError('Dual Farkas solve failed: ' + r.message)
    for scale in (1000, 1000000, 1000000000):
        y = [int(round(scale * v)) for v in r.x]
        for i in range(4):
            mn = min((dot(lp_col(j, a, cap), y) for j, a in ts if j == i), default=0)
            if mn < 0:
                y[i] += -mn
        if dot(y, b) < 0:
            verify_farkas(n, m, cap, y)
            return y
    raise RuntimeError(f'Could not round integer Farkas certificate for {n}, m={m}')


def na_feasible_pair(n, m: int, Tstar: int, du: int, dv: int, cap):
    """Compute exact surviving (t, eT) sets under:
      - Agent 4 baseline NA-DAG constraints (t_a4, eT_a4)
      - Agent 1 + NA-DAG 4-inequality exact pure-integer pruner (t_a1, eT_a1)

    Pure Python integer arithmetic only (zero floating point).
    """
    shift = 38 - Tstar
    c = du + dv - shift
    nt = Tstar
    nx = du - c
    ny = dv - c
    if c < 1 or c > du or nt < 24 or nt > 27:
        return (), (), (), ()
    eT_lo_req = E8[nt]
    eT_hi_req = E8MAX[nt]
    if eT_lo_req > eT_hi_req:
        return (), (), (), ()

    avail = [n[j] for j in range(4)]
    avail[du - 6] -= 1
    avail[dv - 6] -= 1
    if min(avail) < 0:
        return (), (), (), ()

    iu = du - 6
    iv = dv - 6
    ts = local_types(n, m, cap)
    types_u = [a for idx, a in ts if idx == iu]
    types_v = [a for idx, a in ts if idx == iv]
    if not types_u or not types_v:
        return (), (), (), ()

    max_ones_A = du * (10 - du) - (1 if c == 1 else 0)
    max_ones_B = dv * (10 - dv) - (1 if c == 1 else 0)
    max_ones_Y_in_A = nx * (10 - du)
    max_ones_X_in_B = ny * (10 - dv)

    t_konig_lo = max(nx, ny, 2 * ny - max_ones_Y_in_A, 2 * nx - max_ones_X_in_B)
    aT_min_sing = max(nt, 2 * nt - max_ones_A)
    bT_min_sing = max(nt, 2 * nt - max_ones_B)

    t_a4, eT_a4 = set(), set()
    t_a1, eT_a1 = set(), set()

    for s in comps(c, 4):
        if any(s[j] > avail[j] for j in range(4)):
            continue
        ss = dot(s, V)
        st = ss - 2 * c

        bS = -2 * c2(c)
        for j1 in range(4):
            bS += c2(s[j1]) * cap[j1][j1]
            for j2 in range(j1 + 1, 4):
                bS += s[j1] * s[j2] * cap[j1][j2]

        xs = []
        for a in types_u:
            x = tuple(a[j] - s[j] for j in range(4))
            if min(x) >= 0 and all(x[j] + s[j] <= avail[j] for j in range(4)):
                xs.append((x, dot(x, V)))
        if not xs:
            continue

        ys = []
        for a in types_v:
            y = tuple(a[j] - s[j] for j in range(4))
            if min(y) >= 0 and all(y[j] + s[j] <= avail[j] for j in range(4)):
                ys.append((y, dot(y, V)))
        if not ys:
            continue

        for x, sx in xs:
            ux = tuple(s[j] + x[j] for j in range(4))
            bu = -c2(du) - c2(c)
            for j1 in range(4):
                bu += c2(ux[j1]) * cap[j1][j1]
                for j2 in range(j1 + 1, 4):
                    bu += ux[j1] * ux[j2] * cap[j1][j2]

            caps_y_X = [(min(ny, cap[j][iv], V[j] - 1), x[j]) for j in range(4) if x[j] > 0]
            x_ok_a1 = (not any(cp < 1 for cp, _ in caps_y_X))
            forced_ones_X = sum(cnt for cp, cnt in caps_y_X if cp == 1)
            if forced_ones_X > max_ones_X_in_B:
                x_ok_a1 = False
            c_xy1_a1 = sum(cp * cnt for cp, cnt in caps_y_X) if x_ok_a1 else -1

            c_xy1_a4 = sum(x[j] * min(ny, cap[j][iv]) for j in range(4))

            for y, sy in ys:
                z = tuple(avail[j] - s[j] - x[j] - y[j] for j in range(4))
                if min(z) < 0:
                    continue

                c_xy2_a4 = sum(y[j] * min(nx, cap[j][iu]) for j in range(4))
                t_lo_a4 = max(nx, ny)
                t_hi_a4 = min(nx * ny, c_xy1_a4, c_xy2_a4)
                if t_lo_a4 > t_hi_a4:
                    continue

                base = m - ss - sx - sy
                t_lo_a4 = max(t_lo_a4, eT_lo_req - base)
                t_hi_a4 = min(t_hi_a4, eT_hi_req - base)
                if t_lo_a4 > t_hi_a4:
                    continue

                cap_sx = sum(z[j] * min(du, cap[iu][j]) for j in range(4))
                cap_sy = sum(z[j] * min(dv, cap[iv][j]) for j in range(4))
                cap_all = sum(z[j] * (V[j] - (nt - 23)) for j in range(4))
                t_lo_a4 = max(
                    t_lo_a4,
                    st + sx - nx - cap_sx,
                    st + sy - ny - cap_sy,
                    (st + sx - nx + sy - ny - cap_all + 1) // 2,
                )
                t_hi_a4 = min(t_hi_a4, st + sx - nx - nt, st + sy - ny - nt)
                if t_lo_a4 > t_hi_a4:
                    continue

                uy = tuple(s[j] + y[j] for j in range(4))
                bv = -c2(dv) - c2(c)
                for j1 in range(4):
                    bv += c2(uy[j1]) * cap[j1][j1]
                    for j2 in range(j1 + 1, 4):
                        bv += uy[j1] * uy[j2] * cap[j1][j2]

                a4_ts_local = []
                for t in range(t_lo_a4, t_hi_a4 + 1):
                    xt = sx - nx - t
                    yt = sy - ny - t
                    if xt < 0 or yt < 0:
                        continue
                    if min_pairs(st + xt, nt) + min_pairs(t, ny) > bu:
                        continue
                    if min_pairs(st + yt, nt) + min_pairs(t, nx) > bv:
                        continue
                    a4_ts_local.append(t)
                    t_a4.add(t)
                    eT_a4.add(base + t)

                if not a4_ts_local or not x_ok_a1:
                    continue

                caps_S_T = [(min(c, V[j] - (nt - 23)), z[j]) for j in range(4) if z[j] > 0]
                mS_t = min_pairs_capped_from(st, caps_S_T, lb=0, max_at_lb=None)
                if mS_t is None or mS_t > bS:
                    continue

                caps_x_Y = [(min(nx, cap[j][iu], V[j] - 1), y[j]) for j in range(4) if y[j] > 0]
                if any(cp < 1 for cp, _ in caps_x_Y):
                    continue
                forced_ones_Y = sum(cnt for cp, cnt in caps_x_Y if cp == 1)
                if forced_ones_Y > max_ones_Y_in_A:
                    continue
                c_xy2_a1 = sum(cp * cnt for cp, cnt in caps_x_Y)

                caps_A_T = [(min(du, cap[iu][j], V[j] - (nt - 23)), z[j]) for j in range(4) if z[j] > 0]
                caps_B_T = [(min(dv, cap[iv][j], V[j] - (nt - 23)), z[j]) for j in range(4) if z[j] > 0]
                if any(cp < 1 for cp, _ in caps_A_T) or any(cp < 1 for cp, _ in caps_B_T):
                    continue
                forced_ones_AT = sum(cnt for cp, cnt in caps_A_T if cp == 1)
                forced_ones_BT = sum(cnt for cp, cnt in caps_B_T if cp == 1)
                if forced_ones_AT + forced_ones_Y > max_ones_A:
                    continue
                if forced_ones_BT + forced_ones_X > max_ones_B:
                    continue

                t_lo_a1 = max(t_lo_a4, t_konig_lo)
                t_hi_a1 = min(
                    t_hi_a4,
                    c_xy1_a1,
                    c_xy2_a1,
                    st + sx - nx - aT_min_sing,
                    st + sy - ny - bT_min_sing,
                )
                if t_lo_a1 > t_hi_a1:
                    continue

                for t in a4_ts_local:
                    if t < t_lo_a1 or t > t_hi_a1:
                        continue
                    xt = sx - nx - t
                    yt = sy - ny - t
                    aT = st + xt
                    bT = st + yt

                    min_ones_AT = max(forced_ones_AT, 2 * nt - aT)
                    min_ones_Y = max(forced_ones_Y, 2 * ny - t)
                    if min_ones_AT + min_ones_Y > max_ones_A:
                        continue
                    min_ones_BT = max(forced_ones_BT, 2 * nt - bT)
                    min_ones_X = max(forced_ones_X, 2 * nx - t)
                    if min_ones_BT + min_ones_X > max_ones_B:
                        continue

                    mA_T = min_pairs_capped_from(aT, caps_A_T, lb=1, max_at_lb=max_ones_A - min_ones_Y)
                    if mA_T is None:
                        continue
                    mA_Y = min_pairs_capped_from(t, caps_x_Y, lb=1, max_at_lb=min(max_ones_Y_in_A, max_ones_A - min_ones_AT))
                    if mA_Y is None or mA_T + mA_Y > bu:
                        continue

                    mB_T = min_pairs_capped_from(bT, caps_B_T, lb=1, max_at_lb=max_ones_B - min_ones_X)
                    if mB_T is None:
                        continue
                    mB_X = min_pairs_capped_from(t, caps_y_X, lb=1, max_at_lb=min(max_ones_X_in_B, max_ones_B - min_ones_BT))
                    if mB_X is None or mB_T + mB_X > bv:
                        continue

                    t_a1.add(t)
                    eT_a1.add(base + t)

    assert t_a1 <= t_a4 and eT_a1 <= eT_a4
    return tuple(sorted(t_a4)), tuple(sorted(t_a1)), tuple(sorted(eT_a4)), tuple(sorted(eT_a1))


def run_pruner(out_dir: Path, verbose: bool = True):
    t0 = time.monotonic()
    out_dir.mkdir(parents=True, exist_ok=True)

    cap27 = cap_matrix_uniform(27)
    init_p = initial_profiles()
    assert len(init_p) == 931
    surv_all = []
    farkas_base_certs = []
    for n, m in init_p:
        y = check_lp_and_certify(n, m, cap27)
        if y is None:
            surv_all.append((n, m))
        else:
            farkas_base_certs.append({'n': list(n), 'm': m, 'y': y})
    assert len(surv_all) == 543 and len(farkas_base_certs) == 388

    d6_profs = [(n, m) for n, m in surv_all if n[0] > 0]
    d78_profs = [(n, m) for n, m in surv_all if n[0] == 0 and n[3] < 40]
    d9_profs = [(n, m) for n, m in surv_all if n[3] == 40]
    assert len(d6_profs) == 333 and len(d78_profs) == 209 and len(d9_profs) == 1

    cap23 = cap_matrix_uniform(23)
    t23_certs = []
    for n, m in d78_profs:
        y = check_lp_and_certify(n, m, cap23)
        assert y is not None
        t23_certs.append({'n': list(n), 'm': m, 'y': y})
    assert len(t23_certs) == 209

    branches = all_tier2_algebraic_branches()
    branch_reports = []
    pruned_branch_certs = []
    pruned_profile_certs = []

    tot_cand_bp = 0
    tot_lp_kept = 0
    tot_farkas_pruned = 0
    tot_a4_profs = 0
    tot_a1_profs = 0
    tot_a4_triples = 0
    tot_a1_triples = 0

    for br in branches:
        Tstar, du, dv, c = br['Tstar'], br['du'], br['dv'], br['c']
        cap_tb = cap_matrix_tiebroken(Tstar, du, dv)
        lp_kept = 0
        farkas_pruned = 0
        a4_profs = 0
        a1_profs = 0
        a4_triples = 0
        a1_triples = 0
        a4_eT_all = set()
        a1_eT_all = set()
        a1_t_by_eT = {}
        surviving_profiles = []
        farkas_certs_br = []
        a1_only_closed_profs = []

        for n, m in d78_profs:
            need_u = 2 if du == dv else 1
            if n[du - 6] < need_u or n[dv - 6] < need_u:
                continue
            tot_cand_bp += 1
            y = check_lp_and_certify(n, m, cap_tb)
            if y is not None:
                farkas_pruned += 1
                farkas_certs_br.append({'n': list(n), 'm': m, 'y': y})
                continue
            lp_kept += 1
            t4, t1, e4, e1 = na_feasible_pair(n, m, Tstar, du, dv, cap_tb)
            if t4:
                a4_profs += 1
                a4_triples += len(t4)
                a4_eT_all.update(e4)
            if t1:
                a1_profs += 1
                a1_triples += len(t1)
                a1_eT_all.update(e1)
                surviving_profiles.append({
                    'n': list(n), 'm': m, 't': list(t1), 'eT': list(e1),
                })
                for ev in e1:
                    if ev not in a1_t_by_eT:
                        a1_t_by_eT[ev] = [min(t1), max(t1)]
                    else:
                        a1_t_by_eT[ev][0] = min(a1_t_by_eT[ev][0], min(t1))
                        a1_t_by_eT[ev][1] = max(a1_t_by_eT[ev][1], max(t1))
            else:
                a1_only_closed_profs.append({'n': list(n), 'm': m, 'was_a4_open': bool(t4)})

        tot_lp_kept += lp_kept
        tot_farkas_pruned += farkas_pruned
        tot_a4_profs += a4_profs
        tot_a1_profs += a1_profs
        tot_a4_triples += a4_triples
        tot_a1_triples += a1_triples

        status = 'CLOSED_PURE_INTEGER' if a1_profs == 0 else 'SURVIVING'
        if a1_profs == 0:
            pruned_branch_certs.append({
                'branch_id': br['branch_id'],
                'Tstar': Tstar, 'du': du, 'dv': dv, 'c': c,
                'reason': 'FARKAS_EMPTY' if lp_kept == 0 else 'AGENT1_PURE_INTEGER_EMPTY',
                'farkas_pruned': farkas_pruned,
                'a1_closed_lp_kept': len(a1_only_closed_profs),
                'farkas_certs': farkas_certs_br,
                'a1_closed_profiles': a1_only_closed_profs,
            })
        if a1_only_closed_profs:
            pruned_profile_certs.append({
                'branch_id': br['branch_id'],
                'Tstar': Tstar, 'du': du, 'dv': dv, 'c': c,
                'closed_count': len(a1_only_closed_profs),
                'a4_was_open_count': sum(1 for x in a1_only_closed_profs if x['was_a4_open']),
                'profiles': a1_only_closed_profs,
            })

        rec = {
            **br,
            'status': status,
            'lp_kept': lp_kept,
            'farkas_pruned': farkas_pruned,
            'a4_surviving_profiles': a4_profs,
            'a1_surviving_profiles': a1_profs,
            'a1_closed_from_a4': a4_profs - a1_profs,
            'a4_triples': a4_triples,
            'a1_triples': a1_triples,
            'a4_eT_range': [min(a4_eT_all), max(a4_eT_all)] if a4_eT_all else None,
            'a1_eT_range': [min(a1_eT_all), max(a1_eT_all)] if a1_eT_all else None,
            'a1_eT_values': sorted(a1_eT_all),
            'a1_t_range': [
                min(min(p['t']) for p in surviving_profiles),
                max(max(p['t']) for p in surviving_profiles),
            ] if surviving_profiles else None,
            'a1_t_by_eT': {str(k): v for k, v in sorted(a1_t_by_eT.items())},
            'surviving_profiles_detail': surviving_profiles,
        }
        branch_reports.append(rec)
        if verbose:
            rng_s = f"[{rec['a1_eT_range'][0]},{rec['a1_eT_range'][1]}]" if rec['a1_eT_range'] else 'EMPTY'
            print(
                f"  {br['branch_id']:18s} | LP={lp_kept:3d} | A4={a4_profs:3d} ({a4_triples:4d}) "
                f"-> A1={a1_profs:3d} ({a1_triples:4d}) | e(T)={rng_s:8s} | {status}",
                flush=True,
            )

    surviving_branches = [b for b in branch_reports if b['status'] == 'SURVIVING']
    closed_branches = [b for b in branch_reports if b['status'] == 'CLOSED_PURE_INTEGER']

    certs_obj = {
        'schema': 1,
        'engine': 'd78-nadag-exact-integer-pruner-v1',
        'tier2_total_algebraic_branches': len(branches),
        'closed_branch_count': len(closed_branches),
        'surviving_branch_count': len(surviving_branches),
        'closed_branch_ids': [b['branch_id'] for b in closed_branches],
        't23_d78_farkas_certs_count': len(t23_certs),
        't23_d78_farkas_certs': t23_certs,
        'closed_branch_certs': pruned_branch_certs,
        'pruned_profile_certs': pruned_profile_certs,
    }
    certs_path = out_dir / 'd78_nadag_certificates.json'
    certs_path.write_text(json.dumps(certs_obj, separators=(',', ':')) + '\n')
    certs_sha = hashlib.sha256(certs_path.read_bytes()).hexdigest()

    branch_summary_rows = [
        {k: v for k, v in b.items() if k != 'surviving_profiles_detail'}
        for b in branch_reports
    ]

    summary = {
        'schema': 1,
        'engine': 'd78-nadag-exact-integer-pruner-v1',
        'profiles': {
            'initial': 931,
            'farkas_excluded': 388,
            'surviving_all': 543,
            'd6': 333,
            'd78': 209,
            'd9': 1,
        },
        'tier2_d78': {
            'algebraic_branches': len(branches),
            'agent4_nonempty_branches': sum(1 for b in branch_reports if b['a4_surviving_profiles'] > 0),
            'agent1_closed_branches': len(closed_branches),
            'agent1_surviving_branches': len(surviving_branches),
            'closed_branch_ids': [b['branch_id'] for b in closed_branches],
            'candidate_branch_profile_pairs': tot_cand_bp,
            'farkas_pruned_branch_profile_pairs': tot_farkas_pruned,
            'lp_kept_branch_profile_pairs': tot_lp_kept,
            'a4_surviving_branch_profile_pairs': tot_a4_profs,
            'a1_surviving_branch_profile_pairs': tot_a1_profs,
            'a1_closed_branch_profile_pairs_from_a4': tot_a4_profs - tot_a1_profs,
            'a4_triples': tot_a4_triples,
            'a1_triples': tot_a1_triples,
            'triples_removed_vs_a4': tot_a4_triples - tot_a1_triples,
            'pct_triples_removed_vs_a4': round(100.0 * (tot_a4_triples - tot_a1_triples) / max(1, tot_a4_triples), 2),
        },
        'branches': branch_summary_rows,
        'certificates_sha256': certs_sha,
        'elapsed_seconds': round(time.monotonic() - t0, 3),
    }

    summary_path = out_dir / 'd78_nadag_pruning_summary.json'
    summary_path.write_text(json.dumps(summary, indent=2) + '\n')

    manifest_path = out_dir / 'd78_nadag_manifest.json'
    manifest_path.write_text(json.dumps({
        'schema': 1,
        'surviving_branches': [
            {k: v for k, v in b.items() if k != 'surviving_profiles_detail'}
            for b in surviving_branches
        ],
    }, indent=2) + '\n')

    if verbose:
        print(json.dumps(summary['tier2_d78'], indent=2), flush=True)
    return summary


def verify_certificates_pure_integer(out_dir: Path) -> dict:
    """Independent zero-solver pure-integer verifier (Python stdlib only)."""
    t0 = time.monotonic()
    summary = json.loads((out_dir / 'd78_nadag_pruning_summary.json').read_text())
    certs_path = out_dir / 'd78_nadag_certificates.json'
    assert hashlib.sha256(certs_path.read_bytes()).hexdigest() == summary['certificates_sha256']
    certs = json.loads(certs_path.read_text())

    cap23 = cap_matrix_uniform(23)
    for rec in certs['t23_d78_farkas_certs']:
        verify_farkas(tuple(rec['n']), rec['m'], cap23, rec['y'])
    assert len(certs['t23_d78_farkas_certs']) == 209

    closed_br_verified = 0
    for cb in certs['closed_branch_certs']:
        cap_tb = cap_matrix_tiebroken(cb['Tstar'], cb['du'], cb['dv'])
        for fc in cb['farkas_certs']:
            verify_farkas(tuple(fc['n']), fc['m'], cap_tb, fc['y'])
        for pc in cb['a1_closed_profiles']:
            _, t1, _, _ = na_feasible_pair(tuple(pc['n']), pc['m'], cb['Tstar'], cb['du'], cb['dv'], cap_tb)
            assert len(t1) == 0, f"Failed to verify empty {cb['branch_id']} on {pc}"
        closed_br_verified += 1

    pruned_prof_verified = 0
    for pb in certs['pruned_profile_certs']:
        cap_tb = cap_matrix_tiebroken(pb['Tstar'], pb['du'], pb['dv'])
        for pc in pb['profiles']:
            _, t1, _, _ = na_feasible_pair(tuple(pc['n']), pc['m'], pb['Tstar'], pb['du'], pb['dv'], cap_tb)
            assert len(t1) == 0, f"Failed to verify pruned profile {pb['branch_id']} {pc}"
            pruned_prof_verified += 1

    return {
        'status': 'PURE_INTEGER_VERIFICATION_PASSED',
        't23_farkas_verified': len(certs['t23_d78_farkas_certs']),
        'closed_branches_verified': closed_br_verified,
        'pruned_branch_profiles_verified': pruned_prof_verified,
        'verify_seconds': round(time.monotonic() - t0, 3),
    }


def main():
    ap = argparse.ArgumentParser(description='Tier-2 D78 NA-DAG Exact Pure-Integer Pruner & Verifier')
    ap.add_argument('--out-dir', type=Path, default=Path('out_d78_pruner'))
    ap.add_argument('--verify-only', action='store_true')
    ap.add_argument('--quiet', action='store_true')
    args = ap.parse_args()

    if args.verify_only:
        res = verify_certificates_pure_integer(args.out_dir)
        print(json.dumps(res, indent=2), flush=True)
    else:
        run_pruner(args.out_dir, verbose=not args.quiet)
        res = verify_certificates_pure_integer(args.out_dir)
        print(json.dumps(res, indent=2), flush=True)


if __name__ == '__main__':
    main()
