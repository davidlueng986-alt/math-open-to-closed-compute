#!/usr/bin/env python3
r"""V8 Compact 297-variable D9-C7 DIMACS CNF encoder, verifier, and proof-first Kissat/DRAT/LRAT driver.

For a fixed (3,8; 27, 85) triangle-free graph T with alpha(T) <= 7:
  - Roots 0, 1 are nonadjacent with codegree c = 7 (global max nonedge codegree).
  - S = N(0) & N(1) (|S| = 7), X = N(0)\N(1) (|X| = 2), Y = N(1)\N(0) (|Y| = 2), T (|T| = 27).
  - e(T) = 81 + e(X,Y) >= 85 and e(X,Y) <= 4 force e(X,Y) = 4 (K_{2,2}) and e(T) = 85.
  - Only 11 x 27 = 297 edge variables M[r][t] (r in S+X+Y, t in T) remain unfixed!

All encoded constraints are proved necessary conditions (zero heuristic pruning):
  1. Triangle-free with T: 11 * 85 = 935 binary clauses.
  2. Exact row degrees: deg_T(s) = 7 for s in S, deg_T(x) = deg_T(y) = 6 for x in X, y in Y.
  3. Exact column degrees: sum_{r=0..10} M[r][t] = 9 - d_T(t).
  4. Exact X/Y disjointness (from K_{2,2} triangle-freeness): U_X & U_Y = empty.
  5. Exact S-domination (from alpha <= 9 on A=S+X, B=S+Y and U_X & U_Y = empty):
       d_S(t) >= max(1, (9 - d_T(t)) - 2) for every t in T.
  6. Exact X/Y -> T saturation (nonedge codegree >= 1):
       for x in X, t in T: M[x][t] OR uy[t] OR OR_{u in N_T(t)} M[x][u] (and symmetric for Y).
  7. Pairwise codegree caps (<= 7): |N_T(s1)&N_T(s2)| <= 5, |N_T(x1)&N_T(x2)| <= 4, |N_T(y1)&N_T(y2)| <= 4,
     plus only NONTRIVIAL nonadjacent T-pair caps where codeg_T(u,v) + min(rem[u], rem[v]) > 7.
  8. Exact Hall b=1 private-neighbor caps: for each s in S, at most 1 vertex t in T has N_A(t)={s}
     (and at most 1 has N_B(t)={s}), since 2 such vertices + A\{s} would form an I10.
  9. Optional Hall b=2 caps (<= 3 vertices in T with N_A(t) subset {r1, r2}) and optional
     static I7(T) hitting-set constraints (for every W in I7(T), at most 2 of A miss W, and <= 2 of B miss W).
 10. Sound lex symmetry breaking: S[0]<...<S[6], X[0]<X[1], Y[0]<Y[1], X[0]<Y[0]
     (strict < holds because pairwise codegree caps are strictly smaller than row degrees and U_X & U_Y = empty).
"""
import argparse, gzip, hashlib, itertools, json, os, resource, shutil, subprocess, sys, time
from pathlib import Path

N_T = 27
N_G = 40

def decode_g6(raw: str):
    s = raw.strip().removeprefix('>>graph6<<')
    n = ord(s[0]) - 63
    assert n == N_T and len(s) == 1 + (n * (n - 1) // 2 + 5) // 6, f"Bad graph6: {s[:20]}"
    adj = [0] * n
    k = 0
    for j in range(n):
        for i in range(j):
            if ((ord(s[1 + k // 6]) - 63) >> (5 - k % 6)) & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return adj

def enum_indep(adj, k, limit=None):
    n = len(adj)
    res = []
    def dfs(cand, rem, cur):
        if limit is not None and len(res) >= limit:
            return
        if rem == 0:
            res.append(cur)
            return
        while cand.bit_count() >= rem:
            if limit is not None and len(res) >= limit:
                return
            b = cand & -cand
            v = b.bit_length() - 1
            cand ^= b
            dfs(cand & ~adj[v], rem - 1, cur | b)
    dfs((1 << n) - 1, k, 0)
    return res

def verify_r38_27_85(adj):
    assert len(adj) == N_T
    edges = sum(x.bit_count() for x in adj) // 2
    assert edges == 85, f"Expected 85 edges, got {edges}"
    for i in range(N_T):
        assert not ((adj[i] >> i) & 1)
        for j in range(i + 1, N_T):
            assert ((adj[i] >> j) & 1) == ((adj[j] >> i) & 1)
            if (adj[i] >> j) & 1:
                assert (adj[i] & adj[j]) == 0, f"Triangle on ({i},{j})"
    assert len(enum_indep(adj, 8, limit=1)) == 0, "Graph has an independent 8-set"

class CompactCNF:
    def __init__(self, start_var=1):
        self.nv = start_var - 1
        self.clauses = []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        self.clauses.append(list(cl))

    def atmost_seq(self, xs, k):
        m = len(xs)
        if k < 0:
            self.add([])
            return
        if k >= m:
            return
        if k == 0:
            for x in xs:
                self.add([-x])
            return
        # Sinz sequential counter (exact upper bound <= k)
        s = [[self.var() for _ in range(k)] for _ in range(m - 1)]
        self.add([-xs[0], s[0][0]])
        for j in range(1, k):
            self.add([-s[0][j]])
        for i in range(1, m - 1):
            self.add([-xs[i], s[i][0]])
            self.add([-s[i - 1][0], s[i][0]])
            for j in range(1, k):
                self.add([-xs[i], -s[i - 1][j - 1], s[i][j]])
                self.add([-s[i - 1][j], s[i][j]])
            self.add([-xs[i], -s[i - 1][k - 1]])
        self.add([-xs[m - 1], -s[m - 2][k - 1]])

    def atleast_seq(self, xs, k):
        self.atmost_seq([-x for x in xs], len(xs) - k)

    def exact_seq(self, xs, k):
        self.atmost_seq(xs, k)
        self.atleast_seq(xs, k)

    def lex_lt(self, a, b):
        """Enforce bitvector a < b strictly (MSB at index 0)."""
        p = None
        for x, y in zip(a, b):
            pre = [] if p is None else [-p]
            self.add(pre + [-x, y])
            z = self.var()
            if p is not None:
                self.add([-z, p])
            self.add([-z, -x, y])
            self.add([-z, x, -y])
            self.add(pre + [-x, -y, z])
            self.add(pre + [x, y, z])
            p = z
        self.add([-p])

    def write_dimacs(self, path: Path, extra_clauses=()):
        total = len(self.clauses) + len(extra_clauses)
        with open(path, 'w') as f:
            f.write(f"p cnf {self.nv} {total}\n")
            for cl in self.clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')
            for cl in extra_clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')

def build_d9c7_cnf(adj, include_b2=True, include_i7=True, include_lex=True):
    verify_r38_27_85(adj)
    edges = [(i, j) for i in range(N_T) for j in range(i + 1, N_T) if (adj[i] >> j) & 1]
    deg = [x.bit_count() for x in adj]
    rem = [9 - d for d in deg]

    cnf = CompactCNF(1)
    # Primary variables 1..297: M[r][t] = r * 27 + t + 1
    # Rows 0..6 = S, 7..8 = X, 9..10 = Y
    M = [[cnf.var() for _ in range(N_T)] for _ in range(11)]

    # 1. Triangle-free with T
    for r in range(11):
        for u, v in edges:
            cnf.add([-M[r][u], -M[r][v]])

    # 2. Exact row degrees
    for r in range(7):
        cnf.exact_seq(M[r], 7)
    for r in range(7, 11):
        cnf.exact_seq(M[r], 6)

    # 3. Exact column degrees + S-domination + X/Y disjointness
    ux = [cnf.var() for _ in range(N_T)]
    uy = [cnf.var() for _ in range(N_T)]
    for t in range(N_T):
        cnf.exact_seq([M[r][t] for r in range(11)], rem[t])
        cnf.atleast_seq([M[r][t] for r in range(7)], max(1, rem[t] - 2))
        cnf.add([-M[7][t], ux[t]])
        cnf.add([-M[8][t], ux[t]])
        cnf.add([-ux[t], M[7][t], M[8][t]])
        cnf.add([-M[9][t], uy[t]])
        cnf.add([-M[10][t], uy[t]])
        cnf.add([-uy[t], M[9][t], M[10][t]])
        cnf.add([-ux[t], -uy[t]])

    # 4. Saturation X/Y -> T (nonedge codegree >= 1)
    for t in range(N_T):
        nbrs = [u for u in range(N_T) if (adj[t] >> u) & 1]
        for r in (7, 8):
            cnf.add([M[r][t], uy[t]] + [M[r][u] for u in nbrs])
        for r in (9, 10):
            cnf.add([M[r][t], ux[t]] + [M[r][u] for u in nbrs])

    # 5. Pairwise codegree caps (S: <=5, X: <=4, Y: <=4) + nontrivial T-pair caps
    def add_pair_cap(r1, r2, cap):
        bs = []
        for t in range(N_T):
            b = cnf.var()
            cnf.add([-M[r1][t], -M[r2][t], b])
            bs.append(b)
        cnf.atmost_seq(bs, cap)

    for i in range(7):
        for j in range(i + 1, 7):
            add_pair_cap(i, j, 5)
    add_pair_cap(7, 8, 4)
    add_pair_cap(9, 10, 4)

    nontrivial_t_pairs = 0
    for u in range(N_T):
        for v in range(u + 1, N_T):
            if (adj[u] >> v) & 1:
                continue
            ct = (adj[u] & adj[v]).bit_count()
            cap = 7 - ct
            if min(rem[u], rem[v]) > cap:
                nontrivial_t_pairs += 1
                bs = []
                for r in range(11):
                    b = cnf.var()
                    cnf.add([-M[r][u], -M[r][v], b])
                    bs.append(b)
                cnf.atmost_seq(bs, cap)

    # 6. Hall b=1 private-neighbor bounds (exact, 1 clause per (s,t))
    A_rows = list(range(9))
    B_rows = list(range(7)) + [9, 10]
    for s in range(7):
        privA, privB = [], []
        otherA = [r for r in A_rows if r != s]
        otherB = [r for r in B_rows if r != s]
        for t in range(N_T):
            pa = cnf.var()
            cnf.add([-M[s][t], pa] + [M[r][t] for r in otherA])
            privA.append(pa)
            pb = cnf.var()
            cnf.add([-M[s][t], pb] + [M[r][t] for r in otherB])
            privB.append(pb)
        cnf.atmost_seq(privA, 1)
        cnf.atmost_seq(privB, 1)

    # 7. Optional Hall b=2 bounds
    if include_b2:
        for grp in (A_rows, B_rows):
            for i1 in range(len(grp)):
                for i2 in range(i1 + 1, len(grp)):
                    r1, r2 = grp[i1], grp[i2]
                    if set((r1, r2)) in ({7, 8}, {9, 10}):
                        continue
                    omit = [r for r in grp if r != r1 and r != r2]
                    hs = []
                    for t in range(N_T):
                        h = cnf.var()
                        cnf.add([h] + [M[r][t] for r in omit])
                        hs.append(h)
                    cnf.atmost_seq(hs, 3)

    # 8. Optional static I7(T) hitting-set constraints
    i7_count = 0
    if include_i7:
        I7 = enum_indep(adj, 7)
        i7_count = len(I7)
        for w in I7:
            vs = [t for t in range(N_T) if (w >> t) & 1]
            ms = []
            for r in range(11):
                z = cnf.var()
                cnf.add([z] + [M[r][t] for t in vs])
                ms.append(z)
            cnf.atmost_seq(ms[0:9], 2)
            cnf.atmost_seq(ms[0:7] + [ms[9], ms[10]], 2)

    # 9. Sound lex symmetry breaking
    if include_lex:
        for i in range(6):
            cnf.lex_lt(M[i], M[i + 1])
        cnf.lex_lt(M[7], M[8])
        cnf.lex_lt(M[9], M[10])
        cnf.lex_lt(M[7], M[9])

    meta = {
        'vars': cnf.nv,
        'clauses': len(cnf.clauses),
        'nontrivial_t_pairs': nontrivial_t_pairs,
        'i7_count': i7_count,
        'include_b2': include_b2,
        'include_i7': include_i7,
        'include_lex': include_lex,
    }
    return cnf, M, meta

def build_40_graph(adj_T, rows):
    g = [0] * N_G
    def add_e(u, v):
        g[u] |= 1 << v
        g[v] |= 1 << u
    for s in range(2, 9):
        add_e(0, s); add_e(1, s)
    for x in (9, 10):
        add_e(0, x)
        for y in (11, 12):
            add_e(x, y)
    for y in (11, 12):
        add_e(1, y)
    for i in range(N_T):
        for j in range(i + 1, N_T):
            if (adj_T[i] >> j) & 1:
                add_e(13 + i, 13 + j)
    for r in range(11):
        u = 2 + r
        m = rows[r]
        for t in range(N_T):
            if (m >> t) & 1:
                add_e(u, 13 + t)
    return g

def sha256_file(path: Path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()

def extract_4_cores(g6_gz_path: Path):
    """Extract and independently verify all 4 (3,8;27,85) graphs from McKay's r38_27.g6.gz."""
    total = 0
    selected = []
    opener = gzip.open if str(g6_gz_path).endswith('.gz') else open
    with opener(g6_gz_path, 'rt', encoding='ascii') as fp:
        for line in fp:
            s = line.strip().removeprefix('>>graph6<<')
            if not s:
                continue
            assert len(s) == 60 and ord(s[0]) - 63 == 27
            total += 1
            if sum((ord(ch) - 63).bit_count() for ch in s[1:]) == 85:
                adj = decode_g6(s)
                verify_r38_27_85(adj)
                selected.append(s)
    assert total == 477142, f"Expected 477142 graphs in r38_27.g6.gz, got {total}"
    assert len(selected) == 4 and len(set(selected)) == 4
    return selected

def proof_first_solve_core(g6: str, out_dir: Path, seconds: int = 1800, include_b2=True, include_i7=True):
    """Proof-first single-pass Kissat + drat-trim + lrat-check loop for one (3,8;27,85) core."""
    out_dir.mkdir(parents=True, exist_ok=True)
    adj = decode_g6(g6)
    cnf, M, meta = build_d9c7_cnf(adj, include_b2=include_b2, include_i7=include_i7, include_lex=True)
    extra_cuts = []
    seen_cuts = set()
    t0 = time.monotonic()
    iters = 0
    report = {'g6': g6, 'meta': meta, 'status': 'OPEN', 'iters': 0, 'cuts': 0}

    while time.monotonic() - t0 < seconds:
        iters += 1
        rem_sec = max(5, int(seconds - (time.monotonic() - t0)))
        cnf_path = out_dir / 'leaf.cnf'
        drat_path = out_dir / 'leaf.drat'
        lrat_path = out_dir / 'leaf.lrat'
        cnf.write_dimacs(cnf_path, extra_cuts)

        def cap_fsize():
            resource.setrlimit(resource.RLIMIT_FSIZE, (1024 * 1024 ** 2, 1024 * 1024 ** 2))

        t_solve0 = time.monotonic()
        with open(out_dir / 'kissat.log', 'w') as log:
            r = subprocess.run(
                ['kissat', f'--time={rem_sec}', str(cnf_path), str(drat_path)],
                stdout=log, stderr=subprocess.STDOUT, timeout=rem_sec + 30, preexec_fn=cap_fsize
            )
        solve_sec = time.monotonic() - t_solve0
        if r.returncode == 20:
            # UNSAT with native DRAT proof already emitted in the same pass!
            cnf_sha = sha256_file(cnf_path)
            drat_sha = sha256_file(drat_path)
            t_ver0 = time.monotonic()
            with open(out_dir / 'drat-trim.log', 'w') as log:
                v = subprocess.run(
                    ['drat-trim', str(cnf_path), str(drat_path), '-L', str(lrat_path)],
                    stdout=log, stderr=subprocess.STDOUT, timeout=max(60, rem_sec)
                )
            ok_drat = (v.returncode == 0 and 's VERIFIED' in (out_dir / 'drat-trim.log').read_text(errors='replace'))
            ok_lrat = False
            lrat_sha = None
            if ok_drat and lrat_path.exists() and shutil.which('lrat-check'):
                with open(out_dir / 'lrat-check.log', 'w') as log:
                    lv = subprocess.run(
                        ['lrat-check', str(cnf_path), str(lrat_path)],
                        stdout=log, stderr=subprocess.STDOUT, timeout=max(60, rem_sec)
                    )
                ok_lrat = (lv.returncode == 0 and 's VERIFIED' in (out_dir / 'lrat-check.log').read_text(errors='replace'))
                if ok_lrat:
                    lrat_sha = sha256_file(lrat_path)
                    with open(lrat_path, 'rb') as fi, gzip.open(out_dir / 'leaf.lrat.gz', 'wb', compresslevel=1) as fo:
                        shutil.copyfileobj(fi, fo)
            ver_sec = time.monotonic() - t_ver0
            if ok_drat:
                with open(drat_path, 'rb') as fi, gzip.open(out_dir / 'leaf.drat.gz', 'wb', compresslevel=1) as fo:
                    shutil.copyfileobj(fi, fo)
                report.update(
                    status='CERTIFIED_UNSAT', iters=iters, cuts=len(extra_cuts),
                    cnf_sha256=cnf_sha, drat_sha256=drat_sha, lrat_verified=ok_lrat,
                    lrat_sha256=lrat_sha, solve_seconds=round(solve_sec, 3), verify_seconds=round(ver_sec, 3)
                )
            else:
                report.update(status='UNSAT_VERIFICATION_FAILED', iters=iters, cuts=len(extra_cuts))
            drat_path.unlink(missing_ok=True)
            lrat_path.unlink(missing_ok=True)
            break
        elif r.returncode == 10:
            # SAT: parse model and separate I10 cuts
            drat_path.unlink(missing_ok=True)
            vals = set()
            for line in (out_dir / 'kissat.log').read_text(errors='replace').splitlines():
                if line.startswith('v '):
                    for tok in line.split()[1:]:
                        lit = int(tok)
                        if lit > 0 and lit <= 297:
                            vals.add(lit)
            rows = [sum((1 << t) for t in range(N_T) if M[r][t] in vals) for r in range(11)]
            g40 = build_40_graph(adj, rows)
            i10s = enum_indep(g40, 10, limit=128)
            if not i10s:
                (out_dir / 'witness.txt').write_text(
                    ''.join(''.join(str((g40[i] >> j) & 1) for j in range(N_G)) + '\n' for i in range(N_G))
                )
                report.update(status='WITNESS_PENDING_INDEPENDENT_REPLAY', iters=iters, cuts=len(extra_cuts))
                break
            added = 0
            for mask in i10s:
                rs = tuple(v - 2 for v in range(2, 13) if (mask >> v) & 1)
                ts = tuple(v - 13 for v in range(13, 40) if (mask >> v) & 1)
                key = (rs, ts)
                if key not in seen_cuts:
                    seen_cuts.add(key)
                    cl = [M[r][t] for r in rs for t in ts]
                    assert cl, "Empty I10 cut!"
                    extra_cuts.append(cl)
                    added += 1
            assert added > 0
            report.update(iters=iters, cuts=len(extra_cuts))
        else:
            drat_path.unlink(missing_ok=True)
            report.update(status='OPEN_TIMEOUT', kissat_exit=r.returncode, iters=iters, cuts=len(extra_cuts))
            break

    report['total_seconds'] = round(time.monotonic() - t0, 3)
    (out_dir / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)
    return report

def selftest():
    # Exhaustive truth-table check of CompactCNF.atmost_seq and lex_lt (pure Python brute-force checker!)
    def check_sat(nv, clauses, fixed):
        for bits in range(1 << nv):
            ok = True
            for v, val in fixed.items():
                if ((bits >> (v - 1)) & 1) != val:
                    ok = False
                    break
            if not ok:
                continue
            for cl in clauses:
                sat = False
                for lit in cl:
                    v = abs(lit) - 1
                    b = (bits >> v) & 1
                    if (lit > 0 and b == 1) or (lit < 0 and b == 0):
                        sat = True
                        break
                if not sat:
                    ok = False
                    break
            if ok:
                return True
        return False

    for n in range(1, 5):
        for k in range(n + 1):
            c = CompactCNF(1)
            xs = [c.var() for _ in range(n)]
            c.atmost_seq(xs, k)
            for b in itertools.product((0, 1), repeat=n):
                fixed = {i + 1: b[i] for i in range(n)}
                assert check_sat(c.nv, c.clauses, fixed) == (sum(b) <= k), (n, k, b)

    for n in range(1, 4):
        c = CompactCNF(1)
        x = [c.var() for _ in range(n)]
        y = [c.var() for _ in range(n)]
        c.lex_lt(x, y)
        for b in itertools.product((0, 1), repeat=2 * n):
            fixed = {i + 1: b[i] for i in range(2 * n)}
            assert check_sat(c.nv, c.clauses, fixed) == (b[:n] < b[n:]), (n, b)

    sample_g6 = 'ZI_eD@@EOCG@dGO?OBGCeC?GRDC?gQW?yOCOI@a?gQCd@WOIGH_@g?L@oh??'
    adj = decode_g6(sample_g6)
    cnf, M, meta = build_d9c7_cnf(adj, include_b2=True, include_i7=True)
    assert meta['i7_count'] == 750 and meta['nontrivial_t_pairs'] == 0
    print(f"PASS: selftest verified seqcounter, lex_lt, and real (3,8;27,85) CNF {meta}", flush=True)

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--selftest', action='store_true')
    p.add_argument('--g6', help='Single 27-vertex (3,8;27,85) graph6 string')
    p.add_argument('--g6-file', help='Path to McKay r38_27.g6.gz')
    p.add_argument('--out', default='out_d9c7')
    p.add_argument('--seconds', type=int, default=1800)
    p.add_argument('--no-b2', action='store_true')
    p.add_argument('--no-i7', action='store_true')
    a = p.parse_args()
    if a.selftest:
        selftest()
    elif a.g6:
        proof_first_solve_core(a.g6, Path(a.out), a.seconds, not a.no_b2, not a.no_i7)
    elif a.g6_file:
        cores = extract_4_cores(Path(a.g6_file))
        for idx, g6 in enumerate(cores):
            proof_first_solve_core(g6, Path(a.out) / f'core-{idx}', a.seconds, not a.no_b2, not a.no_i7)
    else:
        p.print_help()
