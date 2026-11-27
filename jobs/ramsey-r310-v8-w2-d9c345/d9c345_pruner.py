#!/usr/bin/env python3
r"""Exact pure-integer pruner, canonical skeleton orbit enumerator, and Farkas certificate
generator + independent zero-solver verifier for Ramsey R(3,10) D9 cases c in {3, 4, 5}.

Context:
  In D9, G is a 9-regular triangle-free 40-vertex graph with alpha(G) <= 9 and global
  maximum non-edge codegree c in {3, 4, 5, 6, 7}. Fixing a non-adjacent pair {u, v} with
  codeg(u, v) = c partitions V(G) into:
    - {u, v} (size 2)
    - S = N(u) & N(v) (size c; every s in S has d_T(s) = 7)
    - X = N(u) \ N(v) (size nX = 9 - c; every x in X has d_T(x) = 8 - d_Y(x))
    - Y = N(v) \ N(u) (size nX = 9 - c; every y in Y has d_T(y) = 8 - d_X(y))
    - T = V \ ({u,v} u S u X u Y) (size nT = 20 + c, alpha(T) <= 7, e(T) = 18 + 9c + e(X,Y))

Proved necessary pure-integer pruning layers (zero heuristic pruning):
  1. Non-edge saturation & global max codegree on H = G[X, Y]:
     For every x in X, codeg_G(x, v) = d_Y(x) in [1, c]; symmetrically d_X(y) in [1, c].
     Thus e(X, Y) in [max(e(3,8,nT) - 18 - 9c, nX), nX * min(nX, c)].
  2. Pairwise codegree on H:
     |N_Y(x1) & N_Y(x2)| <= c - 1 and |N_X(y1) & N_X(y2)| <= c - 1 (since x1,x2 share u).
  3. Hall b=1 and b=2 on H:
     - At most 1 x in X has N_Y(x) = {y} for each y in Y (and symmetric).
     - At most 3 x in X have N_Y(x) subset {y1, y2} for each pair {y1, y2} in Y (and symmetric).
  4. Exact skeleton-specific (s, I_X, I_Y) vertex-type linear system over t in T:
     Every infeasible canonical skeleton orbit is certified by an EXACT INTEGER Farkas vector
     y = (y_eq, y_ub) with y_ub >= 0 (all Python ints), independently verified with zero
     floating-point arithmetic and zero external libraries.
"""
import argparse
import hashlib
import itertools
import json
import time
from pathlib import Path

EMIN_R38 = {23: 49, 24: 56, 25: 65, 26: 73, 27: 85}


def c2(n: int) -> int:
    return n * (n - 1) // 2


def dot(a, b) -> int:
    return sum(x * y for x, y in zip(a, b))


def waterfill_min_c2(total: int, caps_counts, lb: int = 0, max_at_lb=None):
    """Exact integer minimum of sum_i C(d_i, 2) subject to lb <= d_i <= cap_i,
    sum d_i = total, and #{i : d_i == lb} <= max_at_lb (if given). Returns None if infeasible."""
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
    if max_at_lb is not None:
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
        take = rem if rem < avail else avail
        cost += take * lvl
        rem -= take
        lvl += 1
    return cost


def rows_to_cols(rows, nX: int):
    return [sum(((rows[i] >> j) & 1) << i for i in range(nX)) for j in range(nX)]


def canon_bipartite(rows, nX: int):
    """Exact canonical representative of an nX x nX bipartite graph under
    S_{nX}(X) x S_{nX}(Y) x Z_2(swap X <-> Y).
    Bucket-preserving column permutations (grouped by column degree) preserve isomorphism
    equivalence classes exactly while running 20x-90x faster than full nX! search.
    """
    cols = rows_to_cols(rows, nX)
    best = None
    for src, opp in ((rows, cols), (cols, rows)):
        # Group column indices by their degree in src (i.e. popcount of opp[j])
        buckets = {}
        for j in range(nX):
            d = opp[j].bit_count()
            buckets.setdefault(d, []).append(j)
        deg_sig = tuple(sorted(buckets.keys()))
        # Build column permutation generator only within equal-degree buckets
        ordered_groups = [buckets[d] for d in deg_sig]
        bucket_perms = [list(itertools.permutations(g)) for g in ordered_groups]
        for prod in itertools.product(*bucket_perms):
            # col_order[new_pos] = old_col
            col_order = [j for grp in prod for j in grp]
            inv_col = [0] * nX
            for new_j, old_j in enumerate(col_order):
                inv_col[old_j] = new_j
            tr = []
            for r in src:
                nr = 0
                tmp = r
                while tmp:
                    b = tmp & -tmp
                    old_j = b.bit_length() - 1
                    tmp ^= b
                    nr |= 1 << inv_col[old_j]
                tr.append(nr)
            tr.sort()
            cand = (tuple(opp[j].bit_count() for j in col_order), tuple(tr))
            if best is None or cand < best:
                best = cand
    return best[1]


def check_skeleton_local(rows, c: int) -> bool:
    """Pure-integer check of all local necessary conditions on H = G[X, Y]."""
    nX = 9 - c
    if len(rows) != nX:
        return False
    cols = rows_to_cols(rows, nX)
    # 1. Saturation & max codegree: 1 <= deg <= c
    if any(not (1 <= r.bit_count() <= c) for r in rows):
        return False
    if any(not (1 <= col.bit_count() <= c) for col in cols):
        return False
    # 2. Pairwise codegree <= c - 1
    for i in range(nX):
        for j in range(i + 1, nX):
            if (rows[i] & rows[j]).bit_count() > c - 1:
                return False
            if (cols[i] & cols[j]).bit_count() > c - 1:
                return False
    # 3. Hall b=1 on X and Y
    r_sing = [r for r in rows if r.bit_count() == 1]
    if len(r_sing) != len(set(r_sing)):
        return False
    c_sing = [col for col in cols if col.bit_count() == 1]
    if len(c_sing) != len(set(c_sing)):
        return False
    # 4. Hall b=2 on X and Y (at most 3 vertices in opposite side contained in any 2-subset)
    for p1 in range(nX):
        for p2 in range(p1 + 1, nX):
            pair = (1 << p1) | (1 << p2)
            if sum(1 for r in rows if (r & ~pair) == 0) > 3:
                return False
            if sum(1 for col in cols if (col & ~pair) == 0) > 3:
                return False
    # 5. Edge count vs e(3,8,nT) and max T-degree <= 7
    nT = 20 + c
    exy = sum(r.bit_count() for r in rows)
    eT = 18 + 9 * c + exy
    if eT < EMIN_R38[nT] or eT > (7 * nT) // 2:
        return False
    return True


def enumerate_canonical_skeletons(c: int):
    """Exact pure-Python enumeration of all canonical valid bipartite skeletons H = G[X, Y]
    for D9-C{c} (c in {3, 4, 5, 6, 7})."""
    nX = 9 - c
    valid_rows = [r for r in range(1, 1 << nX) if 1 <= r.bit_count() <= c]
    valid_rows.sort(key=lambda r: (r.bit_count(), r))
    col_degs = [0] * nX
    chosen = []
    orbits = set()

    # Precompute bit lists for speed
    row_bits = {r: [j for j in range(nX) if (r >> j) & 1] for r in valid_rows}
    row_pc = {r: r.bit_count() for r in valid_rows}

    def dfs(start_idx: int, sing_mask: int):
        depth = len(chosen)
        if depth == nX:
            if any(d == 0 for d in col_degs):
                return
            if not check_skeleton_local(chosen, c):
                return
            orbits.add(canon_bipartite(chosen, nX))
            return
        rem = nX - depth
        zeros = sum(1 for d in col_degs if d == 0)
        if zeros > rem * c:
            return
        for idx in range(start_idx, len(valid_rows)):
            r = valid_rows[idx]
            pc = row_pc[r]
            if pc == 1 and (sing_mask & r):
                continue
            bits_r = row_bits[r]
            ok = True
            for j in bits_r:
                if col_degs[j] + 1 > c:
                    ok = False
                    break
            if not ok:
                continue
            for prev in chosen:
                if (prev & r).bit_count() > c - 1:
                    ok = False
                    break
            if not ok:
                continue
            chosen.append(r)
            for j in bits_r:
                col_degs[j] += 1
            dfs(idx, sing_mask | (r if pc == 1 else 0))
            for j in bits_r:
                col_degs[j] -= 1
            chosen.pop()

    dfs(0, 0)
    ordered = sorted(orbits, key=lambda tup: (sum(r.bit_count() for r in tup), tup))
    return ordered


def build_skeleton_linear_system(c: int, rows):
    """Build exact pure-integer linear system (types, eq_rows, eq_rhs, ub_rows, ub_rhs)
    over vertex-type counts N_{s, I_X, I_Y} >= 0 for t in T, given skeleton H = rows.
    Every coefficient and RHS is an exact Python int.
    """
    nX = 9 - c
    nT = 20 + c
    cols = rows_to_cols(rows, nX)
    exy = sum(r.bit_count() for r in rows)
    eT = 18 + 9 * c + exy

    bad_xx = [
        (1 << i) | (1 << j)
        for i in range(nX) for j in range(i + 1, nX)
        if (rows[i] & rows[j]).bit_count() >= c - 1
    ]
    bad_yy = [
        (1 << i) | (1 << j)
        for i in range(nX) for j in range(i + 1, nX)
        if (cols[i] & cols[j]).bit_count() >= c - 1
    ]

    types = []
    fullY = (1 << nX) - 1
    for ix in range(1 << nX):
        a = ix.bit_count()
        if a > c:
            continue
        if any((ix & p) == p for p in bad_xx):
            continue
        forbY = 0
        for i in range(nX):
            if (ix >> i) & 1:
                forbY |= rows[i]
        allowY = fullY ^ forbY
        iy = allowY
        while True:
            b = iy.bit_count()
            if b <= c and not any((iy & p) == p for p in bad_yy):
                for s in range(c + 1):
                    if not (1 <= s + a <= c and 1 <= s + b <= c):
                        continue
                    dt = 9 - s - a - b
                    if not (max(0, c - 3) <= dt <= 7):
                        continue
                    types.append((s, ix, iy, a, b, dt))
            if iy == 0:
                break
            iy = (iy - 1) & allowY

    # Equalities: A_eq @ N == b_eq
    eq_rows = [[1 for _ in types], [t[0] for t in types]]
    eq_rhs = [nT, 7 * c]
    for i in range(nX):
        eq_rows.append([1 if (t[1] >> i) & 1 else 0 for t in types])
        eq_rhs.append(8 - rows[i].bit_count())
    for j in range(nX):
        eq_rows.append([1 if (t[2] >> j) & 1 else 0 for t in types])
        eq_rhs.append(8 - cols[j].bit_count())

    # Inequalities: A_ub @ N <= b_ub
    ub_rows = []
    ub_rhs = []

    # 1. S-S, S-X, S-Y pairwise codegrees
    ub_rows.append([c2(t[0]) for t in types])
    ub_rhs.append(c2(c) * (c - 2))
    for i in range(nX):
        ub_rows.append([t[0] if (t[1] >> i) & 1 else 0 for t in types])
        ub_rhs.append(c * (c - 1))
    for j in range(nX):
        ub_rows.append([t[0] if (t[2] >> j) & 1 else 0 for t in types])
        ub_rhs.append(c * (c - 1))

    # 2. Exact X-X and Y-Y pairwise codegrees in T
    for i in range(nX):
        for j in range(i + 1, nX):
            pair = (1 << i) | (1 << j)
            ub_rows.append([1 if (t[1] & pair) == pair else 0 for t in types])
            ub_rhs.append(c - 1 - (rows[i] & rows[j]).bit_count())
            ub_rows.append([1 if (t[2] & pair) == pair else 0 for t in types])
            ub_rhs.append(c - 1 - (cols[i] & cols[j]).bit_count())

    # 3. Exact X-Y non-edge codegrees in T: 1 <= codeg_T(x, y) <= c
    for i in range(nX):
        for j in range(nX):
            if not ((rows[i] >> j) & 1):
                cv = [1 if (((t[1] >> i) & 1) and ((t[2] >> j) & 1)) else 0 for t in types]
                ub_rows.append(cv)
                ub_rhs.append(c)
                ub_rows.append([-v for v in cv])
                ub_rhs.append(-1)

    # 4. Exact Hall b=1 on A = S u X and B = S u Y
    ub_rows.append([1 if (t[0] == 1 and t[3] == 0) else 0 for t in types])
    ub_rhs.append(c)
    ub_rows.append([1 if (t[0] == 1 and t[4] == 0) else 0 for t in types])
    ub_rhs.append(c)
    for i in range(nX):
        used_in_Y = sum(1 for j in range(nX) if cols[j] == (1 << i))
        ub_rows.append([1 if (t[0] == 0 and t[1] == (1 << i)) else 0 for t in types])
        ub_rhs.append(1 - used_in_Y)
    for j in range(nX):
        used_in_X = sum(1 for i in range(nX) if rows[i] == (1 << j))
        ub_rows.append([1 if (t[0] == 0 and t[2] == (1 << j)) else 0 for t in types])
        ub_rhs.append(1 - used_in_X)

    # 5. Exact Hall b=2 on X-pairs and Y-pairs
    for i in range(nX):
        for j in range(i + 1, nX):
            pair = (1 << i) | (1 << j)
            used_Y = sum(1 for y in range(nX) if (cols[y] & ~pair) == 0)
            ub_rows.append([1 if (t[0] == 0 and (t[1] & ~pair) == 0) else 0 for t in types])
            ub_rhs.append(3 - used_Y)
            used_X = sum(1 for x in range(nX) if (rows[x] & ~pair) == 0)
            ub_rows.append([1 if (t[0] == 0 and (t[2] & ~pair) == 0) else 0 for t in types])
            ub_rhs.append(3 - used_X)

    # 6. T non-edge codegree sum identity
    sum_dtx = sum(c2(8 - r.bit_count()) for r in rows)
    sum_dty = sum(c2(8 - col.bit_count()) for col in cols)
    ub_rows.append([c2(t[5]) for t in types])
    ub_rhs.append(c * (c2(nT) - eT) - 21 * c - sum_dtx - sum_dty)

    return types, eq_rows, eq_rhs, ub_rows, ub_rhs


def verify_farkas_certificate(c: int, rows, y_eq, y_ub) -> bool:
    """Independent ZERO-SOLVER pure-integer verifier for a skeleton Farkas certificate.
    Proves that no N >= 0 satisfies A_eq @ N == b_eq and A_ub @ N <= b_ub:
      1. All entries of y_eq and y_ub are exact Python ints.
      2. All entries of y_ub are >= 0.
      3. For every column j (valid (s, I_X, I_Y) type): (y_eq^T A_eq + y_ub^T A_ub)_j >= 0.
      4. y_eq^T b_eq + y_ub^T b_ub < 0.
    """
    types, eq_rows, eq_rhs, ub_rows, ub_rhs = build_skeleton_linear_system(c, rows)
    if len(y_eq) != len(eq_rhs) or len(y_ub) != len(ub_rhs):
        return False
    if not all(type(v) is int for v in y_eq):
        return False
    if not all(type(v) is int and v >= 0 for v in y_ub):
        return False
    rhs_val = dot(y_eq, eq_rhs) + dot(y_ub, ub_rhs)
    if rhs_val >= 0:
        return False
    n_vars = len(types)
    for j in range(n_vars):
        col_val = sum(y_eq[r] * eq_rows[r][j] for r in range(len(eq_rows)))
        col_val += sum(y_ub[r] * ub_rows[r][j] for r in range(len(ub_rows)))
        if col_val < 0:
            return False
    return True


def find_farkas_certificate(c: int, rows):
    """Attempt to certify skeleton H = rows infeasible via an exact integer Farkas vector.
    Returns (y_eq, y_ub) if provably infeasible (and independently verified!), or None if feasible.
    """
    import numpy as np
    from scipy.optimize import linprog

    types, eq_rows, eq_rhs, ub_rows, ub_rhs = build_skeleton_linear_system(c, rows)
    n_eq = len(eq_rhs)
    n_ub = len(ub_rhs)
    if not types:
        y_eq = [-1] + [0] * (n_eq - 1)
        y_ub = [0] * n_ub
        assert verify_farkas_certificate(c, rows, y_eq, y_ub)
        return y_eq, y_ub

    A_eq = np.asarray(eq_rows, dtype=float)
    b_eq = np.asarray(eq_rhs, dtype=float)
    A_ub = np.asarray(ub_rows, dtype=float)
    b_ub = np.asarray(ub_rhs, dtype=float)

    res = linprog(np.zeros(len(types)), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=(0, None), method='highs')
    if res.status == 0:
        return None
    if res.status != 2:
        raise RuntimeError(f"Unexpected LP status {res.status}: {res.message}")

    # Solve dual Farkas LP:
    #   -A_eq^T y_eq - A_ub^T y_ub <= 0,  b_eq^T y_eq + b_ub^T y_ub <= -1,  y_ub >= 0
    A_all = np.vstack([A_eq, A_ub])
    b_all = np.concatenate([b_eq, b_ub])
    dual_A = np.vstack([-A_all.T, b_all.reshape(1, -1)])
    dual_b = np.concatenate([np.zeros(len(types)), np.array([-1.0])])
    bounds = [(None, None)] * n_eq + [(0.0, None)] * n_ub
    r_dual = linprog(np.zeros(n_eq + n_ub), A_ub=dual_A, b_ub=dual_b, bounds=bounds, method='highs')
    if not r_dual.success:
        raise RuntimeError(f"Dual Farkas LP failed: {r_dual.message}")

    # Exact integer rounding + row-0 (sum N = nT) slack repair
    for scale in (100, 1000, 100000, 10000000, 1000000000):
        y_eq = [int(round(scale * v)) for v in r_dual.x[:n_eq]]
        y_ub = [max(0, int(round(scale * v))) for v in r_dual.x[n_eq:]]
        # Since eq_rows[0] is all 1s, adding delta >= 0 to y_eq[0] shifts every column sum by +delta
        min_col = 0
        for j in range(len(types)):
            cv = sum(y_eq[r] * eq_rows[r][j] for r in range(n_eq))
            cv += sum(y_ub[r] * ub_rows[r][j] for r in range(n_ub))
            if cv < min_col:
                min_col = cv
        if min_col < 0:
            y_eq[0] += -min_col
        if dot(y_eq, eq_rhs) + dot(y_ub, ub_rhs) < 0:
            assert verify_farkas_certificate(c, rows, y_eq, y_ub)
            return y_eq, y_ub
    raise RuntimeError("Failed to round dual Farkas vector to exact integers")


def run_pruner(cases=(5, 4, 3), out_dir: Path = None):
    t0 = time.monotonic()
    summary = {'schema': 1, 'engine': 'd9c345-exact-integer-pruner-v1', 'cases': {}}
    cert_bundle = {'schema': 1, 'engine': 'd9c345-exact-integer-pruner-v1', 'cases': {}}

    for c in cases:
        tc0 = time.monotonic()
        nX = 9 - c
        nT = 20 + c
        raw_lo = EMIN_R38[nT] - 18 - 9 * c
        raw_hi = nX * nX
        sat_lo = max(raw_lo, nX)
        sat_hi = min(nX * min(nX, c), (7 * nT) // 2 - 18 - 9 * c)

        orbits = enumerate_canonical_skeletons(c)
        surviving = []
        pruned_certs = []
        surv_by_e = {}
        pruned_by_e = {}

        for idx, rows in enumerate(orbits):
            exy = sum(r.bit_count() for r in rows)
            oid = f"D9-C{c}-S{idx:04d}"
            cert = find_farkas_certificate(c, rows)
            if cert is None:
                surv_by_e[exy] = surv_by_e.get(exy, 0) + 1
                surviving.append({
                    'id': oid,
                    'c': c,
                    'nX': nX,
                    'nT': nT,
                    'e_xy': exy,
                    'e_T': 18 + 9 * c + exy,
                    'rows': list(rows),
                })
            else:
                y_eq, y_ub = cert
                pruned_by_e[exy] = pruned_by_e.get(exy, 0) + 1
                pruned_certs.append({
                    'id': oid,
                    'c': c,
                    'e_xy': exy,
                    'e_T': 18 + 9 * c + exy,
                    'rows': list(rows),
                    'y_eq': y_eq,
                    'y_ub': y_ub,
                })

        surv_e_vals = sorted(surv_by_e.keys())
        closed_e_by_sat = [e for e in range(raw_lo, raw_hi + 1) if e < sat_lo or e > sat_hi]
        closed_e_by_farkas = [e for e in range(sat_lo, sat_hi + 1) if e not in surv_by_e]

        case_sum = {
            'c': c,
            'nX': nX,
            'nT': nT,
            'raw_e_xy_range': [raw_lo, raw_hi],
            'raw_e_xy_count': raw_hi - raw_lo + 1,
            'sat_e_xy_range': [sat_lo, sat_hi],
            'surviving_e_xy_range': [surv_e_vals[0], surv_e_vals[-1]] if surv_e_vals else [],
            'surviving_e_xy_count': len(surv_e_vals),
            'closed_e_xy_by_saturation': closed_e_by_sat,
            'closed_e_xy_by_farkas': closed_e_by_farkas,
            'valid_canonical_orbits': len(orbits),
            'farkas_pruned_orbits': len(pruned_certs),
            'surviving_orbits': len(surviving),
            'surviving_by_e_xy': {str(k): surv_by_e[k] for k in sorted(surv_by_e)},
            'pruned_by_e_xy': {str(k): pruned_by_e[k] for k in sorted(pruned_by_e)},
            'runtime_seconds': round(time.monotonic() - tc0, 3),
        }
        summary['cases'][f'C{c}'] = case_sum
        cert_bundle['cases'][f'C{c}'] = {
            'c': c,
            'valid_canonical_orbits': len(orbits),
            'farkas_pruned_count': len(pruned_certs),
            'surviving_count': len(surviving),
            'pruned_certificates': pruned_certs,
            'surviving_orbits': surviving,
        }

    summary['total_runtime_seconds'] = round(time.monotonic() - t0, 3)

    if out_dir is not None:
        out_dir.mkdir(parents=True, exist_ok=True)
        cert_path = out_dir / 'd9c345_farkas_certificates.json'
        cert_bytes = (json.dumps(cert_bundle, separators=(',', ':')) + '\n').encode('utf-8')
        cert_path.write_bytes(cert_bytes)
        cert_sha = hashlib.sha256(cert_bytes).hexdigest()
        summary['certificates_sha256'] = cert_sha
        sum_path = out_dir / 'd9c345_pruning_summary.json'
        sum_path.write_text(json.dumps(summary, indent=2) + '\n')
    return summary, cert_bundle


def verify_certificate_file(cert_path: Path, summary_path: Path = None):
    """Independent ZERO-SOLVER pure-integer verification of d9c345_farkas_certificates.json."""
    t0 = time.monotonic()
    raw_bytes = cert_path.read_bytes().replace(b'\r\n', b'\n')
    actual_sha = hashlib.sha256(raw_bytes).hexdigest()
    if summary_path is not None and summary_path.exists():
        sum_obj = json.loads(summary_path.read_text())
        assert sum_obj['certificates_sha256'] == actual_sha, "SHA-256 mismatch!"
    bundle = json.loads(raw_bytes.decode('utf-8'))
    total_verified = 0
    per_case = {}
    for ck, cdata in bundle['cases'].items():
        c = cdata['c']
        certs = cdata['pruned_certificates']
        assert len(certs) == cdata['farkas_pruned_count']
        for rec in certs:
            assert rec['c'] == c
            assert check_skeleton_local(rec['rows'], c)
            ok = verify_farkas_certificate(c, rec['rows'], rec['y_eq'], rec['y_ub'])
            assert ok, f"Farkas verification FAILED for {rec['id']}"
            total_verified += 1
        per_case[ck] = {
            'farkas_certs_verified': len(certs),
            'surviving_orbits': len(cdata['surviving_orbits']),
        }
    res = {
        'status': 'INDEPENDENT_PURE_INTEGER_VERIFICATION_PASSED',
        'total_farkas_certs_verified': total_verified,
        'per_case': per_case,
        'certificates_sha256': actual_sha,
        'verify_seconds': round(time.monotonic() - t0, 3),
    }
    return res



def expand_sparse_farkas(c: int, rows, y_eq_nz, y_ub_nz):
    _, eq_rows, _, ub_rows, _ = build_skeleton_linear_system(c, rows)
    y_eq = [0] * len(eq_rows)
    y_ub = [0] * len(ub_rows)
    for idx, val in y_eq_nz:
        assert type(idx) is int and type(val) is int and 0 <= idx < len(y_eq)
        y_eq[idx] = val
    for idx, val in y_ub_nz:
        assert type(idx) is int and type(val) is int and 0 <= idx < len(y_ub)
        y_ub[idx] = val
    return y_eq, y_ub


def verify_sparse_certificate_file(sparse_path: Path, summary_path: Path = None):
    """Independent ZERO-SOLVER pure-integer verification of d9c345_farkas_sparse.json."""
    t0 = time.monotonic()
    raw_bytes = sparse_path.read_bytes().replace(b'\r\n', b'\n')
    actual_sha = hashlib.sha256(raw_bytes).hexdigest()
    if summary_path is not None and summary_path.exists():
        sum_obj = json.loads(summary_path.read_text())
        if 'sparse_certificates_sha256' in sum_obj:
            assert sum_obj['sparse_certificates_sha256'] == actual_sha, "Sparse SHA-256 mismatch!"
    bundle = json.loads(raw_bytes.decode('utf-8'))
    total_verified = 0
    per_case = {}
    for ck, cdata in bundle['cases'].items():
        c = cdata['c']
        certs = cdata['pruned_certificates']
        assert len(certs) == cdata['farkas_pruned_count']
        for rec in certs:
            assert check_skeleton_local(rec['rows'], c)
            y_eq, y_ub = expand_sparse_farkas(c, rec['rows'], rec['y_eq_nz'], rec['y_ub_nz'])
            assert verify_farkas_certificate(c, rec['rows'], y_eq, y_ub), f"Farkas verification FAILED for {rec['id']}"
            total_verified += 1
        per_case[ck] = {
            'farkas_certs_verified': len(certs),
            'surviving_count': cdata['surviving_count'],
        }
    return {
        'status': 'INDEPENDENT_PURE_INTEGER_VERIFICATION_PASSED',
        'format': 'sparse_exact_integer_farkas',
        'total_farkas_certs_verified': total_verified,
        'per_case': per_case,
        'sparse_certificates_sha256': actual_sha,
        'verify_seconds': round(time.monotonic() - t0, 3),
    }


def build_surviving_manifest_stdlib(sparse_path: Path, case_selector: str, out_path: Path):
    """Pure-stdlib (zero scipy) builder of surviving orbits manifest from verified sparse Farkas certs."""
    t0 = time.monotonic()
    bundle = json.loads(sparse_path.read_text())
    keys = [k for k in ('C5', 'C4', 'C3') if k in bundle['cases']] if case_selector == 'ALL' else [case_selector]
    out_cases = {}
    for ck in keys:
        if ck == 'C6' and 'C6' not in bundle['cases']:
            orbits = enumerate_canonical_skeletons(6)
            assert len(orbits) == 12
            surviving = [
                {
                    'id': f"D9-C6-S{idx:04d}",
                    'c': 6,
                    'nX': 3,
                    'nT': 26,
                    'e_xy': sum(r.bit_count() for r in rows),
                    'e_T': 72 + sum(r.bit_count() for r in rows),
                    'rows': list(rows),
                }
                for idx, rows in enumerate(orbits)
            ]
            out_cases['C6'] = {'c': 6, 'surviving_orbits': surviving}
            continue
        cdata = bundle['cases'][ck]
        c = cdata['c']
        nX, nT = 9 - c, 20 + c
        pruned_set = set()
        for rec in cdata['pruned_certificates']:
            y_eq, y_ub = expand_sparse_farkas(c, rec['rows'], rec['y_eq_nz'], rec['y_ub_nz'])
            assert verify_farkas_certificate(c, rec['rows'], y_eq, y_ub), f"Bad cert {rec['id']}"
            pruned_set.add(tuple(rec['rows']))
        orbits = enumerate_canonical_skeletons(c)
        assert len(orbits) == cdata['valid_canonical_orbits']
        surviving = []
        for idx, rows in enumerate(orbits):
            if rows in pruned_set:
                continue
            exy = sum(r.bit_count() for r in rows)
            surviving.append({
                'id': f"D9-C{c}-S{idx:04d}",
                'c': c,
                'nX': nX,
                'nT': nT,
                'e_xy': exy,
                'e_T': 18 + 9 * c + exy,
                'rows': list(rows),
            })
        assert len(surviving) == cdata['surviving_count']
        out_cases[ck] = {'c': c, 'surviving_orbits': surviving}
    manifest = {
        'schema': 1,
        'case_selector': case_selector,
        'cases': out_cases,
        'build_seconds': round(time.monotonic() - t0, 3),
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(manifest, separators=(',', ':')) + '\n')
    return manifest


def main():
    ap = argparse.ArgumentParser(description='D9-C3/C4/C5 exact integer pruner & Farkas verifier')
    ap.add_argument('--cases', default='5,4,3', help='Comma-separated c values (default: 5,4,3)')
    ap.add_argument('--out-dir', type=Path, default=Path('out_pruner'))
    ap.add_argument('--verify', action='store_true', help='Run independent zero-solver verifier on --out-dir')
    ap.add_argument('--build-manifest', default=None, choices=['C6', 'C5', 'C4', 'C3', 'ALL'],
                    help='Pure-stdlib manifest builder for surviving orbits using verified sparse certs')
    ap.add_argument('--manifest-out', type=Path, default=Path('out/orbits_manifest.json'))
    args = ap.parse_args()

    if args.build_manifest:
        m = build_surviving_manifest_stdlib(
            args.out_dir / 'd9c345_farkas_sparse.json', args.build_manifest, args.manifest_out
        )
        print(json.dumps({
            'status': 'MANIFEST_BUILT_STDLIB',
            'case': args.build_manifest,
            'counts': {k: len(v['surviving_orbits']) for k, v in m['cases'].items()},
            'build_seconds': m['build_seconds'],
        }, indent=2), flush=True)
        return

    if args.verify:
        full_p = args.out_dir / 'd9c345_farkas_certificates.json'
        sparse_p = args.out_dir / 'd9c345_farkas_sparse.json'
        sum_p = args.out_dir / 'd9c345_pruning_summary.json'
        if full_p.exists():
            res = verify_certificate_file(full_p, sum_p)
        else:
            res = verify_sparse_certificate_file(sparse_p, sum_p)
        print(json.dumps(res, indent=2), flush=True)
        return

    cases = tuple(int(x.strip()) for x in args.cases.split(',') if x.strip())
    summary, _ = run_pruner(cases=cases, out_dir=args.out_dir)
    print(json.dumps(summary, indent=2), flush=True)
    # Immediately run independent zero-solver verification
    ver = verify_certificate_file(
        args.out_dir / 'd9c345_farkas_certificates.json',
        args.out_dir / 'd9c345_pruning_summary.json',
    )
    print(json.dumps(ver, indent=2), flush=True)


if __name__ == '__main__':
    main()
