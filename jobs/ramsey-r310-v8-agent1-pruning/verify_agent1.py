#!/usr/bin/env python3
"""Independent pure-integer verifier for Agent 1 Ramsey R(3,10) certificates.

Uses ONLY Python standard library (zero SciPy/NumPy/OR-Tools/floating-point dependencies).
Independently checks:
  1. All 388 v6 profile Farkas certificates and exact partition of all 931 profiles (when v6_profile_cert.json is present).
  2. Every closed-task certificate in agent1_closed_tasks_certificates.json by independently
     checking the SHA-256 v7 task key and enumerating all compatible (x, y) pairs to verify
     exact integer refutation for every t in [tlo, thi].
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
ET = {23: 35, 24: 40, 25: 46, 26: 52, 27: 61, 28: 68}
P = list(itertools.combinations_with_replacement(range(4), 2))
D_PAIRS = list(itertools.combinations(range(4), 2))
NE = 4 + len(D_PAIRS)


@lru_cache(None)
def comps(n, k=4):
    if k == 1:
        return ((n,),)
    return tuple((a,) + b for a in range(n + 1) for b in comps(n - a, k - 1))


def dot(a, b):
    return sum(i * j for i, j in zip(a, b))


def c2(n):
    return n * (n - 1) // 2


def waterfill_min_c2(total, caps_counts, lb, max_at_lb):
    """Independent pure-integer implementation of exact capped minimum of sum C(d_i, 2)."""
    n_tot = 0
    cap_sum = 0
    forced_lb = 0
    for cap, cnt in caps_counts:
        if cap < lb:
            return None
        n_tot += cnt
        cap_sum += cap * cnt
        if cap == lb:
            forced_lb += cnt
    if total < lb * n_tot or total > cap_sum:
        return None
    if forced_lb > max_at_lb:
        return None
    if total < lb * n_tot + max(0, n_tot - max_at_lb):
        return None
    rem = total - lb * n_tot
    cost = n_tot * c2(lb)
    lvl = lb
    while rem > 0:
        avail = sum(cnt for cap, cnt in caps_counts if cap > lvl)
        if avail == 0:
            return None
        step = rem if rem < avail else avail
        cost += step * lvl
        rem -= step
        lvl += 1
    return cost


def all_profiles():
    out = set()
    for n in comps(40, 4):
        D = dot(n, (3, 2, 1, 0))
        if D % 2 or D > 38:
            continue
        m = 180 - D // 2
        L = [max(0, 9 * k + E[k] - m) for k in V]
        ok = True
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
                ok = False
                break
        if not ok:
            continue
        if dot(n, L) > sum(n[i] * V[i] * (3 - i) for i in range(4)):
            continue
        if 2 * sum(n[i] * (3 - i) * L[i] for i in range(4)) > D * D:
            continue
        out.add((n, m))
    return out


@lru_cache(None)
def local_types(n, m):
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


def verify_v6_profile_certs(cert_path):
    obj = json.loads(Path(cert_path).read_text())
    expected = all_profiles()
    assert len(expected) == 931
    kept = {(tuple(n), m) for n, m in obj['surviving']}
    excl = {(tuple(c['n']), c['m']) for c in obj['excluded']}
    assert len(kept) == len(obj['surviving']) and len(excl) == len(obj['excluded'])
    assert not (kept & excl) and (kept | excl) == expected
    for c in obj['excluded']:
        n = tuple(c['n'])
        m = c['m']
        y = c['y']
        b = list(n) + [0] * len(D_PAIRS)
        for k, j in P:
            v = n[k] * (n[k] - 1) if k == j else n[k] * n[j]
            b.extend([-v, (V[k] + V[j] - 11) * v])
        assert len(y) == len(b)
        assert all(type(val) is int for val in y)
        assert min(y[NE:]) >= 0
        for i, a in local_types(n, m):
            col = [int(i == j) for j in range(4)] + [
                (a[j] if i == k else 0) - (a[k] if i == j else 0) for k, j in D_PAIRS
            ]
            for k, j in P:
                cap = V[k] + V[j] - 11
                if k == j:
                    cc = a[k] * (a[k] - 1); ed = a[k] if i == k else 0
                else:
                    cc = a[k] * a[j]; ed = a[j] if i == k else 0
                col.extend([-cc - ed, cc + cap * ed])
            assert dot(col, y) >= 0
        assert dot(y, b) < 0
    return kept


def verify_profile_t_impossible(n, m, d, q, tlo, thi):
    """Independently prove NO (x, y, t) with t in [tlo, thi] satisfies the exact integer inequalities."""
    nx, ny, nt = d - 1, q - 1, 40 - d - q
    avail = [n[i] - (V[i] == d) - (V[i] == q) for i in range(4)]
    if min(avail) < 0:
        return True
    ts = local_types(n, m)
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

    for x, sx in xx:
        caps_y_X = [(min(ny, V[i] + q - 12, V[i] - 1), x[i]) for i in range(4) if x[i] > 0]
        if any(c < 0 for c, _ in caps_y_X) or sum(cnt for c, cnt in caps_y_X if c == 0) > 10 - q:
            continue
        bx = (nx - 1) * sx - 12 * c2(nx)
        for y, sy in yy:
            if any(x[i] + y[i] > avail[i] for i in range(4)):
                continue
            caps_x_Y = [(min(nx, V[i] + d - 12, V[i] - 1), y[i]) for i in range(4) if y[i] > 0]
            if any(c < 0 for c, _ in caps_x_Y) or sum(cnt for c, cnt in caps_x_Y if c == 0) > 10 - d:
                continue
            z = [avail[i] - x[i] - y[i] for i in range(4)]
            caps_x_T = [(min(nx, V[i] + d - 11), z[i]) for i in range(4) if z[i] > 0]
            caps_y_T = [(min(ny, V[i] + q - 11), z[i]) for i in range(4) if z[i] > 0]
            by = (ny - 1) * sy - 12 * c2(ny)
            for t in range(tlo, thi + 1):
                if t < max(0, d + q - 11, ET[nt] - m + 1 + sx + sy):
                    continue
                if t > min(nx * ny, sx + nx * (q - 12), sy + ny * (d - 12), 4 * nt - m + 1 + sx + sy):
                    continue
                xt = sx - nx - t
                yt = sy - ny - t
                if xt < max(nt, 2 * nt - nx * (10 - d)):
                    continue
                if yt < max(nt, 2 * nt - ny * (10 - q)):
                    continue
                mx_t = waterfill_min_c2(xt, caps_x_T, 1, nx * (10 - d))
                mx_y = waterfill_min_c2(t, caps_x_Y, 0, 10 - d)
                if mx_t is None or mx_y is None or mx_t + mx_y > bx:
                    continue
                my_t = waterfill_min_c2(yt, caps_y_T, 1, ny * (10 - q))
                my_x = waterfill_min_c2(t, caps_y_X, 0, 10 - q)
                if my_t is None or my_x is None or my_t + my_x > by:
                    continue
                return False
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dir', type=Path, required=True)
    args = ap.parse_args()
    t0 = time.monotonic()

    v6_path = args.dir / 'v6_profile_cert.json'
    kept = None
    if v6_path.exists():
        kept = verify_v6_profile_certs(v6_path)
        assert len(kept) == 543

    closed_path = args.dir / 'agent1_closed_tasks_certificates.json'
    closed_obj = json.loads(closed_path.read_text())
    summary = json.loads((args.dir / 'agent1_pruning_summary.json').read_text())
    assert hashlib.sha256(closed_path.read_bytes()).hexdigest() == summary['closed_certificates_sha256']

    certs = closed_obj['certificates']
    assert len(certs) == closed_obj['closed_task_count'] == summary['v7_tasks']['empty_agent1']
    checked_profiles = 0
    for c in certs:
        task_dict = dict(
            id=c['task'], d=c['d'], q=c['q'], band=c['band'], m=c['m'],
            profiles=c['profiles'], tlo=c['tlo'], thi=c['thi']
        )
        expected_key = hashlib.sha256(json.dumps(task_dict, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        assert c['key'] == expected_key, f"Task key mismatch for {c['task']}"
        for p in c['profiles']:
            n = tuple(p)
            if kept is not None:
                assert (n, c['m']) in kept
            assert verify_profile_t_impossible(n, c['m'], c['d'], c['q'], c['tlo'], c['thi']), \
                f"FAILED verification on {c['task']} profile {n}"
            checked_profiles += 1

    dt = time.monotonic() - t0
    print(json.dumps(dict(
        status="INDEPENDENT_PURE_INTEGER_VERIFICATION_PASSED",
        v6_farkas_checked=(kept is not None),
        closed_tasks_verified=len(certs),
        newly_closed_v7_open_231_verified=closed_obj['newly_closed_from_v7_open_231'],
        profile_instances_verified=checked_profiles,
        verify_seconds=round(dt, 3),
    ), indent=2), flush=True)


if __name__ == '__main__':
    main()
