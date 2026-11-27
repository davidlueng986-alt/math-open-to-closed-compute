#!/usr/bin/env python3
r"""Unified Non-Adjacent-Root DAG Tier-1 D6 Pure-Integer Pruner & Certifier.

Combines:
  - Agent 4's Tier-1 D6 Inner Weighted-Mantel Non-Adjacent-Root Decomposition
    (9 exhaustive branches covering all 333 surviving n_6 >= 1 profiles:
     r in {5, 6, 7}, q in {r+1, ..., 9}, c = q - r, n_T = 32 - r,
     e(3, 8, n_T) <= e(T) <= min(E8MAX[n_T], 132 - 8*r)),
  - Agent 1's 4 exact pure-integer combinatorial inequalities adapted soundly
    to non-adjacent root pairs (u, v) with d_u = 6, d_v = q, codeg(u, v) = c:
      1. Saturation / Konig cross-edge bounds: deg_Y(x) >= 1, deg_X(y) >= 1,
         t = e(X, Y) >= max(n_X, n_Y), plus e(S U X U Y, T) >= n_T + z_9.
      2. Rooted singleton caps on A = S U X and B = S U Y:
         m_Y <= n_X*(10 - d_u), m_X <= n_Y*(10 - q),
         m_Y + m_{T,A} <= d_u*(10 - d_u) - 1[c==1],
         m_X + m_{T,B} <= q*(10 - q) - 1[c==1].
      3. Degree-aware non-edge & shared-root codegree caps on X, Y, and T:
         deg_Y(x) <= min(n_Y, deg(x) + q - 11, deg(x) - 1),
         deg_X(y) <= min(n_X, deg(y) + d_u - 11, deg(y) - 1),
         deg_A(w) <= min(d_u, deg(w) + d_u - 11),
         deg_B(w) <= min(q, deg(w) + q - 11),
         deg_{S U X U Y}(w) in [max(1, deg(w) - 7), deg(w) - (n_T - 23)].
      4. Exact water-filling degree-capped & singleton-capped convexity
         (min_pairs_capped_from) on both A -> (T, Y) and B -> (T, X).

Zero floating-point exclusions: every profile exclusion is certified by a pure-integer
Farkas vector, and every pruned (branch, profile) or (branch, profile, t) triple is
certified by pure integer arithmetic and independently re-verifiable using stdlib only.
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
E8 = {21: 35, 22: 42, 23: 49, 24: 56, 25: 65, 26: 73, 27: 85}
E8MAX = {23: 80, 24: 84, 25: 87, 26: 91, 27: 94}

P_PAIRS = list(itertools.combinations_with_replacement(range(4), 2))
D_PAIRS = list(itertools.combinations(range(4), 2))
NE = 4 + len(D_PAIRS)

# The exact 9 Tier-1 D6 branches (Theorem 1 of Agent 4)
TIER1_D6_BRANCHES = [
    dict(
        id=f"D6-R{r}-Q{q}",
        du=6,
        dv=q,
        r=r,
        q=q,
        c=q - r,
        nx=6 - (q - r),
        ny=r,
        nt=32 - r,
        eT_lo=E8[32 - r],
        eT_hi=min(E8MAX[32 - r], 132 - 8 * r),
    )
    for r in (5, 6, 7)
    for q in range(r + 1, 10)
]
assert len(TIER1_D6_BRANCHES) == 9


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
    if n == 0:
        return 0 if total == 0 else 10**9
    q, r = divmod(total, n)
    return (n - r) * c2(q) + r * c2(q + 1)


def min_pairs_capped_from(total, counts_by_cap, lb=1, max_at_lb=None):
    """Exact integer minimum of sum_i C(d_i, 2) over integer sequences with
    lb <= d_i <= cap_i, sum d_i = total, and (if max_at_lb is not None)
    #{i : d_i == lb} <= max_at_lb.

    Returns (min_cost, min_count_at_lb) or None if infeasible.
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
    avail_above_lb = n_tot - forced_lb
    lifted_from_lb = min(total - lb * n_tot, avail_above_lb)
    min_at_lb = n_tot - lifted_from_lb
    if max_at_lb is not None and min_at_lb > max_at_lb:
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
    return cost, min_at_lb


def initial_profiles():
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


CAP27 = tuple(
    tuple(min(V[i], V[j], V[i] + V[j] - 11) for j in range(4))
    for i in range(4)
)


@lru_cache(None)
def local_types(n, m, cap=CAP27):
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


def lp_col(i, a, cap=CAP27):
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


def lp_rhs(n, cap=CAP27):
    b = list(n) + [0] * len(D_PAIRS)
    for k, j in P_PAIRS:
        c_cap = cap[k][j]
        v = n[k] * (n[k] - 1) if k == j else n[k] * n[j]
        b.extend([-v, c_cap * v])
    return b


def verify_farkas_types(n, ts, y, cap=CAP27):
    b = lp_rhs(n, cap)
    assert len(y) == len(b)
    assert all(type(v) is int for v in y)
    assert min(y[NE:]) >= 0
    assert all(dot(lp_col(i, a, cap), y) >= 0 for i, a in ts)
    assert dot(y, b) < 0
    return True


def check_lp_and_certify(n, m, ts=None, cap=CAP27):
    import numpy as np
    from scipy.optimize import linprog

    if ts is None:
        ts = local_types(n, m, cap)
    b = lp_rhs(n, cap)
    if not ts or any(n[i] and not any(j == i for j, a in ts) for i in range(4)):
        i = next(i for i in range(4) if n[i] and not any(j == i for j, a in ts))
        y = [0] * len(b)
        y[i] = -1
        verify_farkas_types(n, ts, y, cap)
        return y
    A = np.asarray([lp_col(i, a, cap) for i, a in ts], dtype=float).T
    bf = np.asarray(b, dtype=float)
    res = linprog(
        np.zeros(len(ts)),
        A_eq=A[:NE],
        b_eq=bf[:NE],
        A_ub=A[NE:],
        b_ub=bf[NE:],
        bounds=(0, None),
        method="highs",
    )
    if res.status == 0:
        return None
    if res.status != 2:
        raise RuntimeError(f"Unexpected HiGHS status {res.status}: {res.message}")
    r = linprog(
        np.zeros(len(b)),
        A_ub=np.vstack([-A.T, bf]),
        b_ub=np.r_[np.zeros(len(ts)), -1.0],
        bounds=[(None, None)] * NE + [(0, None)] * (len(b) - NE),
        method="highs",
    )
    if not r.success:
        raise RuntimeError("Dual Farkas solve failed: " + r.message)
    for scale in (1000, 1000000, 1000000000):
        y = [int(round(scale * v)) for v in r.x]
        for i in range(4):
            mn = min((dot(lp_col(j, a, cap), y) for j, a in ts if j == i), default=0)
            if mn < 0:
                y[i] += -mn
        if dot(y, b) < 0:
            verify_farkas_types(n, ts, y, cap)
            return y
    raise RuntimeError(f"Could not round integer Farkas certificate for {n}, m={m}")


def screen_d6_branch_profile(n, m, r, q, cap=CAP27):
    """Evaluate a single (D6 profile, Tier-1 branch (r, q)) under both:
      - Agent 4 baseline (uniform convexity, Agent 4 analyze_tiered_v8.cpp)
      - Combined Agent 4 + Agent 1 (4 exact pure-integer inequalities)

    Returns dict with:
      a4_t: sorted list of feasible t values under Agent 4 baseline
      a4_eT: sorted list of feasible e(T) values under Agent 4 baseline
      combined_t: sorted list of feasible t values under Agent 4 + Agent 1
      combined_eT: sorted list of feasible e(T) values under Agent 4 + Agent 1
      combined_pairs: sorted list of (t, eT) pairs under Agent 4 + Agent 1
    """
    du, dv = 6, q
    c = q - r
    nx, ny, nt = du - c, r, 32 - r
    eT_lo = E8[nt]
    eT_hi = min(E8MAX[nt], 132 - 8 * r)
    if c < 1 or c > du or eT_lo > eT_hi:
        return dict(a4_t=[], a4_eT=[], combined_t=[], combined_eT=[], combined_pairs=[])

    avail = [n[j] for j in range(4)]
    avail[du - 6] -= 1
    avail[dv - 6] -= 1
    if min(avail) < 0:
        return dict(a4_t=[], a4_eT=[], combined_t=[], combined_eT=[], combined_pairs=[])

    ts = local_types(n, m, cap)
    iu, iv = du - 6, dv - 6
    types_u = [a for idx, a in ts if idx == iu]
    types_v = [a for idx, a in ts if idx == iv]
    if not types_u or not types_v:
        return dict(a4_t=[], a4_eT=[], combined_t=[], combined_eT=[], combined_pairs=[])

    max_ones_A = du * (10 - du) - (1 if c == 1 else 0)
    max_ones_B = dv * (10 - dv) - (1 if c == 1 else 0)
    max_ones_Y = nx * (10 - du)
    max_ones_X = ny * (10 - dv)

    a4_t_set, a4_eT_set = set(), set()
    comb_t_set, comb_eT_set, comb_pairs = set(), set(), set()

    for s in comps(c, 4):
        if any(s[j] > avail[j] for j in range(4)):
            continue
        ss = dot(s, V)
        st = ss - 2 * c

        xs = []
        for a in types_u:
            x = tuple(a[j] - s[j] for j in range(4))
            if min(x) >= 0 and all(x[j] + s[j] <= avail[j] for j in range(4)):
                xs.append((x, dot(x, V), a))
        if not xs:
            continue

        ys = []
        for a in types_v:
            y = tuple(a[j] - s[j] for j in range(4))
            if min(y) >= 0 and all(y[j] + s[j] <= avail[j] for j in range(4)):
                ys.append((y, dot(y, V), a))
        if not ys:
            continue

        for x, sx, ux in xs:
            # Pairwise codegree upper bound B_A for A = S U X
            bu = -c2(du) - c2(c)
            for j1 in range(4):
                bu += c2(ux[j1]) * cap[j1][j1]
                for j2 in range(j1 + 1, 4):
                    bu += ux[j1] * ux[j2] * cap[j1][j2]

            caps_y_X = [(min(ny, cap[j][iv], V[j] - 1), x[j]) for j in range(4) if x[j] > 0]
            c_xy1 = sum(cp * cnt for cp, cnt in caps_y_X)

            for y, sy, uy in ys:
                z = [avail[j] - s[j] - x[j] - y[j] for j in range(4)]
                if min(z) < 0:
                    continue

                # Inequality 1 & 3 (shared with Agent 4)
                t_lo_xy = max(nx, ny)
                caps_x_Y = [(min(nx, cap[j][iu], V[j] - 1), y[j]) for j in range(4) if y[j] > 0]
                c_xy2 = sum(cp * cnt for cp, cnt in caps_x_Y)
                t_hi_xy = min(nx * ny, c_xy1, c_xy2)
                if t_lo_xy > t_hi_xy:
                    continue

                base = m - ss - sx - sy
                t_lo = max(t_lo_xy, eT_lo - base)
                t_hi = min(t_hi_xy, eT_hi - base)
                if t_lo > t_hi:
                    continue

                cap_sx = sum(z[j] * min(du, cap[iu][j]) for j in range(4))
                cap_sy = sum(z[j] * min(dv, cap[iv][j]) for j in range(4))
                cap_all = sum(z[j] * (V[j] - (nt - 23)) for j in range(4))
                t_lo = max(
                    t_lo,
                    st + sx - nx - cap_sx,
                    st + sy - ny - cap_sy,
                    (st + sx - nx + sy - ny - cap_all + 1) // 2,
                )
                t_hi = min(t_hi, st + sx - nx - nt, st + sy - ny - nt)
                if t_lo > t_hi:
                    continue

                bv = -c2(dv) - c2(c)
                for j1 in range(4):
                    bv += c2(uy[j1]) * cap[j1][j1]
                    for j2 in range(j1 + 1, 4):
                        bv += uy[j1] * uy[j2] * cap[j1][j2]

                # Agent 4 baseline uniform convexity
                a4_valid_ts = []
                for t in range(t_lo, t_hi + 1):
                    xt = sx - nx - t
                    yt = sy - ny - t
                    if xt < 0 or yt < 0:
                        continue
                    if min_pairs(st + xt, nt) + min_pairs(t, ny) > bu:
                        continue
                    if min_pairs(st + yt, nt) + min_pairs(t, nx) > bv:
                        continue
                    a4_valid_ts.append(t)
                    a4_t_set.add(t)
                    a4_eT_set.add(base + t)

                if not a4_valid_ts:
                    continue

                # Agent 1 exact pure-integer inequalities (1..4) for non-adjacent roots
                # 1b. Lower bound on e(S U X U Y, T) from deg_T(w) <= 7 (z[3] deg-9 vertices need >=2 edges)
                min_edge_T = nt + z[3]
                t_hi_a1 = min(t_hi, (st + sx - nx + sy - ny - min_edge_T) // 2)

                # 2. Rooted singleton bounds on e(A, T) and e(B, T) and t
                #    e(A, T) >= 2*nt - max_ones_A; e(B, T) >= 2*nt - max_ones_B
                t_hi_a1 = min(
                    t_hi_a1,
                    st + sx - nx - max(nt, 2 * nt - max_ones_A),
                    st + sy - ny - max(nt, 2 * nt - max_ones_B),
                )
                t_lo_a1 = max(
                    t_lo,
                    2 * ny - max_ones_Y,
                    2 * nx - max_ones_X,
                )
                if t_lo_a1 > t_hi_a1:
                    continue

                # 3. Capped lists for T -> A and T -> B
                caps_a_T = [(min(du, cap[iu][j]), z[j]) for j in range(4) if z[j] > 0]
                caps_b_T = [(min(dv, cap[iv][j]), z[j]) for j in range(4) if z[j] > 0]

                # 4. Exact water-filling degree-capped & singleton-capped convexity
                for t in a4_valid_ts:
                    if not (t_lo_a1 <= t <= t_hi_a1):
                        continue
                    e_AT = st + sx - nx - t
                    e_BT = st + sy - ny - t

                    ra_t = min_pairs_capped_from(e_AT, caps_a_T, lb=1, max_at_lb=max_ones_A)
                    if ra_t is None:
                        continue
                    ra_y = min_pairs_capped_from(t, caps_x_Y, lb=1, max_at_lb=max_ones_Y)
                    if ra_y is None:
                        continue
                    if ra_t[0] + ra_y[0] > bu:
                        continue
                    if ra_t[1] + ra_y[1] > max_ones_A:
                        continue

                    rb_t = min_pairs_capped_from(e_BT, caps_b_T, lb=1, max_at_lb=max_ones_B)
                    if rb_t is None:
                        continue
                    rb_x = min_pairs_capped_from(t, caps_y_X, lb=1, max_at_lb=max_ones_X)
                    if rb_x is None:
                        continue
                    if rb_t[0] + rb_x[0] > bv:
                        continue
                    if rb_t[1] + rb_x[1] > max_ones_B:
                        continue

                    comb_t_set.add(t)
                    comb_eT_set.add(base + t)
                    comb_pairs.add((t, base + t))

    assert comb_t_set <= a4_t_set
    assert comb_eT_set <= a4_eT_set
    return dict(
        a4_t=sorted(a4_t_set),
        a4_eT=sorted(a4_eT_set),
        combined_t=sorted(comb_t_set),
        combined_eT=sorted(comb_eT_set),
        combined_pairs=sorted(comb_pairs),
    )


def verify_d6_certificates_stdlib(cert_obj, plan_obj=None):
    """Independent zero-solver (stdlib-only) pure-integer verifier for:
      1. Exact 931 = 388 Farkas-excluded + 543 surviving profile partition (333 D6).
      2. Exact 207 / 333 D6 profiles forcing e(H_u) <= 121 (Farkas certificates).
      3. Every pruned (branch, profile) pure-integer UNSAT certificate across all 9 Tier-1 D6 branches.
      4. Coverage completeness audit: all 9 branches present, covering all 333 D6 profiles.
    """
    expected = set(initial_profiles())
    assert len(expected) == 931
    excl_profs = set()
    for rec in cert_obj["farkas_excluded_profiles"]:
        n = tuple(rec["n"])
        m = rec["m"]
        y = rec["y"]
        verify_farkas_types(n, local_types(n, m, CAP27), y, CAP27)
        excl_profs.add((n, m))
    surv_profs = {(tuple(n), m) for n, m in cert_obj["surviving_profiles"]}
    assert not (excl_profs & surv_profs)
    assert (excl_profs | surv_profs) == expected
    assert len(excl_profs) == 388 and len(surv_profs) == 543

    d6_profs = sorted(p for p in surv_profs if p[0][0] > 0)
    assert len(d6_profs) == 333

    # Verify 207 forced e(H_u) <= 121 Farkas certificates
    forced_set = set()
    for rec in cert_obj["d6_forced_eH_le_121_certificates"]:
        n = tuple(rec["n"])
        m = rec["m"]
        y = rec["y"]
        assert (n, m) in surv_profs and n[0] > 0
        ts_no_121 = tuple(
            t for t in local_types(n, m, CAP27) if not (t[0] == 0 and m - dot(t[1], V) <= 121)
        )
        verify_farkas_types(n, ts_no_121, y, CAP27)
        forced_set.add((n, m))
    assert len(forced_set) == 207

    # Verify all 9 branches and every pure-integer UNSAT (branch, profile) certificate
    branch_map = {b["id"]: b for b in TIER1_D6_BRANCHES}
    seen_branches = set()
    pruned_verified = 0
    for b_rec in cert_obj["branch_certificates"]:
        bid = b_rec["branch_id"]
        assert bid in branch_map
        seen_branches.add(bid)
        b = branch_map[bid]
        for p_rec in b_rec["pruned_profiles"]:
            n = tuple(p_rec["n"])
            m = p_rec["m"]
            assert (n, m) in surv_profs and n[0] > 0
            res = screen_d6_branch_profile(n, m, b["r"], b["q"])
            assert len(res["combined_t"]) == 0, f"Certificate FAILED for {bid} {n} m={m}"
            pruned_verified += 1
        if plan_obj is not None:
            plan_b = next(x for x in plan_obj["branches"] if x["id"] == bid)
            pruned_set = {(tuple(x["n"]), x["m"]) for x in b_rec["pruned_profiles"]}
            surv_set = {(tuple(x["n"]), x["m"]) for x in plan_b["surviving_profiles"]}
            assert not (pruned_set & surv_set)
            assert (pruned_set | surv_set) == set(d6_profs), f"Incomplete D6 coverage in {bid}"

    assert seen_branches == set(branch_map.keys())
    return dict(
        status="PURE_INTEGER_VERIFICATION_PASSED",
        profiles_total=931,
        farkas_excluded_verified=len(excl_profs),
        d6_profiles_total=len(d6_profs),
        d6_forced_eH_le_121_verified=len(forced_set),
        tier1_branches_verified=len(seen_branches),
        pruned_branch_profile_certs_verified=pruned_verified,
    )


def run_pruner(out_dir: Path, verify: bool = True):
    t0 = time.monotonic()
    out_dir.mkdir(parents=True, exist_ok=True)

    init_p = initial_profiles()
    assert len(init_p) == 931
    farkas_excl = []
    surviving = []
    for n, m in init_p:
        y = check_lp_and_certify(n, m, cap=CAP27)
        if y is None:
            surviving.append((n, m))
        else:
            farkas_excl.append(dict(n=list(n), m=m, y=y))
    assert len(farkas_excl) == 388 and len(surviving) == 543

    d6_profs = [(n, m) for n, m in surviving if n[0] > 0]
    assert len(d6_profs) == 333

    # Certify 207 / 333 D6 profiles forcing e(H_u) <= 121
    forced_121_certs = []
    for n, m in d6_profs:
        ts_no_121 = tuple(
            t for t in local_types(n, m, CAP27) if not (t[0] == 0 and m - dot(t[1], V) <= 121)
        )
        y = check_lp_and_certify(n, m, ts=ts_no_121, cap=CAP27)
        if y is not None:
            forced_121_certs.append(dict(n=list(n), m=m, y=y))
    assert len(forced_121_certs) == 207
    forced_121_set = {(tuple(x["n"]), x["m"]) for x in forced_121_certs}

    # Screen all 9 Tier-1 D6 branches against all 333 D6 profiles
    branch_plans = []
    branch_certs = []
    totals = dict(
        total_branch_profiles=9 * len(d6_profs),
        a4_surviving_branch_profiles=0,
        combined_surviving_branch_profiles=0,
        a4_triples=0,
        combined_triples=0,
        pruned_branch_profiles_total=0,
        newly_pruned_by_agent1_branch_profiles=0,
        closed_branches_a4=0,
        closed_branches_combined=0,
        surviving_branches_combined=0,
        # Also track residual 126 profiles (not forcing e(H_u) <= 121)
        residual126_a4_branch_profiles=0,
        residual126_combined_branch_profiles=0,
        residual126_a4_triples=0,
        residual126_combined_triples=0,
    )

    for b in TIER1_D6_BRANCHES:
        r, q = b["r"], b["q"]
        a4_pc = comb_pc = a4_tc = comb_tc = 0
        res126_a4_pc = res126_comb_pc = res126_a4_tc = res126_comb_tc = 0
        newly_pruned_pc = 0
        surv_list = []
        pruned_list = []
        eT_lo_obs, eT_hi_obs = 999, -1
        t_lo_obs, t_hi_obs = 999, -1
        eT_to_t = {}

        for n, m in d6_profs:
            res = screen_d6_branch_profile(n, m, r, q)
            in_res126 = (n, m) not in forced_121_set
            if res["a4_t"]:
                a4_pc += 1
                a4_tc += len(res["a4_t"])
                if in_res126:
                    res126_a4_pc += 1
                    res126_a4_tc += len(res["a4_t"])
            if res["combined_t"]:
                comb_pc += 1
                comb_tc += len(res["combined_t"])
                if in_res126:
                    res126_comb_pc += 1
                    res126_comb_tc += len(res["combined_t"])
                eT_lo_obs = min(eT_lo_obs, res["combined_eT"][0])
                eT_hi_obs = max(eT_hi_obs, res["combined_eT"][-1])
                t_lo_obs = min(t_lo_obs, res["combined_t"][0])
                t_hi_obs = max(t_hi_obs, res["combined_t"][-1])
                for t_val, eT_val in res["combined_pairs"]:
                    eT_to_t.setdefault(str(eT_val), set()).add(t_val)
                surv_list.append(
                    dict(
                        n=list(n),
                        m=m,
                        forces_eH_le_121=(not in_res126),
                        t_values=res["combined_t"],
                        eT_values=res["combined_eT"],
                    )
                )
            else:
                reason = "AGENT1_EXACT_INTEGER" if res["a4_t"] else "AGENT4_NA_PRUNE"
                if res["a4_t"]:
                    newly_pruned_pc += 1
                pruned_list.append(dict(n=list(n), m=m, reason=reason))

        totals["a4_surviving_branch_profiles"] += a4_pc
        totals["combined_surviving_branch_profiles"] += comb_pc
        totals["a4_triples"] += a4_tc
        totals["combined_triples"] += comb_tc
        totals["pruned_branch_profiles_total"] += len(pruned_list)
        totals["newly_pruned_by_agent1_branch_profiles"] += newly_pruned_pc
        totals["residual126_a4_branch_profiles"] += res126_a4_pc
        totals["residual126_combined_branch_profiles"] += res126_comb_pc
        totals["residual126_a4_triples"] += res126_a4_tc
        totals["residual126_combined_triples"] += res126_comb_tc
        if a4_pc == 0:
            totals["closed_branches_a4"] += 1
        if comb_pc == 0:
            totals["closed_branches_combined"] += 1
        else:
            totals["surviving_branches_combined"] += 1

        eT_t_map = {k: sorted(v) for k, v in sorted(eT_to_t.items(), key=lambda kv: int(kv[0]))}
        branch_plans.append(
            dict(
                **b,
                status="CLOSED_PURE_INTEGER" if comb_pc == 0 else "OPEN_SAT",
                a4_profiles=a4_pc,
                combined_profiles=comb_pc,
                pruned_profiles=len(pruned_list),
                newly_pruned_by_agent1=newly_pruned_pc,
                a4_triples=a4_tc,
                combined_triples=comb_tc,
                residual126_profiles=res126_comb_pc,
                residual126_triples=res126_comb_tc,
                eT_obs=[eT_lo_obs, eT_hi_obs] if comb_pc else None,
                t_obs=[t_lo_obs, t_hi_obs] if comb_pc else None,
                eT_to_t=eT_t_map,
                surviving_profiles=surv_list,
            )
        )
        branch_certs.append(
            dict(
                branch_id=b["id"],
                r=r,
                q=q,
                c=b["c"],
                nt=b["nt"],
                pruned_count=len(pruned_list),
                newly_pruned_by_agent1=newly_pruned_pc,
                pruned_profiles=pruned_list,
            )
        )

    plan_obj = dict(
        schema=1,
        engine="d6-nadag-pruner-v1",
        d6_profiles_total=len(d6_profs),
        d6_forced_eH_le_121=len(forced_121_certs),
        d6_residual_profiles=len(d6_profs) - len(forced_121_certs),
        totals=totals,
        branches=branch_plans,
    )
    cert_obj = dict(
        schema=1,
        engine="d6-nadag-pruner-v1",
        farkas_excluded_profiles=farkas_excl,
        surviving_profiles=[[list(n), m] for n, m in surviving],
        d6_forced_eH_le_121_certificates=forced_121_certs,
        branch_certificates=branch_certs,
    )

    plan_path = out_dir / "d6_nadag_plan.json"
    cert_path = out_dir / "d6_nadag_certificates.json"
    plan_path.write_text(json.dumps(plan_obj, indent=2) + "\n")
    cert_path.write_text(json.dumps(cert_obj, separators=(",", ":")) + "\n")
    cert_sha = hashlib.sha256(cert_path.read_bytes()).hexdigest()

    ver_report = verify_d6_certificates_stdlib(cert_obj, plan_obj) if verify else None
    summary = dict(
        schema=1,
        engine="d6-nadag-pruner-v1",
        elapsed_seconds=round(time.monotonic() - t0, 3),
        certificates_sha256=cert_sha,
        totals=totals,
        branch_summary=[
            dict(
                id=x["id"],
                r=x["r"],
                q=x["q"],
                c=x["c"],
                nt=x["nt"],
                status=x["status"],
                a4_profiles=x["a4_profiles"],
                combined_profiles=x["combined_profiles"],
                newly_pruned_by_agent1=x["newly_pruned_by_agent1"],
                a4_triples=x["a4_triples"],
                combined_triples=x["combined_triples"],
                residual126_profiles=x["residual126_profiles"],
                eT_obs=x["eT_obs"],
                t_obs=x["t_obs"],
            )
            for x in branch_plans
        ],
        independent_verification=ver_report,
    )
    (out_dir / "d6_nadag_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)
    return summary


def main():
    ap = argparse.ArgumentParser(description="Tier-1 D6 Non-Adjacent-Root Exact Integer Pruner & Certifier")
    ap.add_argument("--out-dir", type=Path, default=Path("out_d6_pruner"))
    ap.add_argument("--verify-only", type=Path, help="Verify existing d6_nadag_certificates.json directory (stdlib only)")
    a = ap.parse_args()
    if a.verify_only:
        cert_obj = json.loads((a.verify_only / "d6_nadag_certificates.json").read_text())
        plan_path = a.verify_only / "d6_nadag_plan.json"
        plan_obj = json.loads(plan_path.read_text()) if plan_path.exists() else None
        rep = verify_d6_certificates_stdlib(cert_obj, plan_obj)
        print(json.dumps(rep, indent=2), flush=True)
    else:
        run_pruner(a.out_dir, verify=True)


if __name__ == "__main__":
    main()
