#!/usr/bin/env python3
"""Comprehensive local unit & soundness test suite for D9-C3/C4/C5 pruner, CNF encoder,
witness verifier, and sharded batch runner.

Works both WITH scipy (regenerates fresh Farkas certificates) and WITHOUT scipy
(verifies committed pure-integer certificates using Python stdlib only, e.g. inside math-compute-sat).
"""
import importlib.util
import itertools
import json
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import d9c345_pruner as pruner
import d9c345_compact_cnf as cnf_mod
import d9c345_batch_runner as runner

HAS_SCIPY = importlib.util.find_spec('scipy') is not None


def check_sat_bruteforce(nv: int, clauses, fixed: dict) -> bool:
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
                b = (bits >> (abs(lit) - 1)) & 1
                if (lit > 0 and b == 1) or (lit < 0 and b == 0):
                    sat = True
                    break
            if not sat:
                ok = False
                break
        if ok:
            return True
    return False


def test_cnf_primitives():
    for n in range(1, 5):
        for k in range(n + 1):
            c = cnf_mod.CompactCNF(1)
            xs = [c.var() for _ in range(n)]
            c.atmost_seq(xs, k)
            for b in itertools.product((0, 1), repeat=n):
                fixed = {i + 1: b[i] for i in range(n)}
                assert check_sat_bruteforce(c.nv, c.clauses, fixed) == (sum(b) <= k), (n, k, b)

    for n in range(1, 4):
        c_lt = cnf_mod.CompactCNF(1)
        x = [c_lt.var() for _ in range(n)]
        y = [c_lt.var() for _ in range(n)]
        c_lt.lex_lt(x, y)

        c_le = cnf_mod.CompactCNF(1)
        x2 = [c_le.var() for _ in range(n)]
        y2 = [c_le.var() for _ in range(n)]
        c_le.lex_le(x2, y2)

        for b in itertools.product((0, 1), repeat=2 * n):
            fixed = {i + 1: b[i] for i in range(2 * n)}
            assert check_sat_bruteforce(c_lt.nv, c_lt.clauses, fixed) == (b[:n] < b[n:]), (n, b)
            assert check_sat_bruteforce(c_le.nv, c_le.clauses, fixed) == (b[:n] <= b[n:]), (n, b)

    print("PASS [1/6]: CompactCNF primitives (atmost_seq, lex_lt, lex_le truth tables)", flush=True)


def test_waterfill():
    configs = [
        [(1, 2), (2, 2), (3, 1)],
        [(0, 1), (1, 2), (3, 2)],
        [(2, 2), (4, 1)],
    ]
    for cfg in configs:
        caps = [cap for cap, cnt in cfg for _ in range(cnt)]
        n = len(caps)
        for lb in (0, 1):
            if any(cap < lb for cap in caps):
                assert pruner.waterfill_min_c2(lb * n, cfg, lb=lb) is None
                continue
            for max_lb in range(n + 1):
                best = {}
                for tup in itertools.product(*(range(lb, cap + 1) for cap in caps)):
                    if sum(v == lb for v in tup) > max_lb:
                        continue
                    s = sum(tup)
                    val = sum(pruner.c2(v) for v in tup)
                    if s not in best or val < best[s]:
                        best[s] = val
                for tot in range(sum(caps) + 2):
                    assert pruner.waterfill_min_c2(tot, cfg, lb=lb, max_at_lb=max_lb) == best.get(tot)
    print("PASS [2/6]: waterfill_min_c2 exactness vs exhaustive brute force", flush=True)


def test_skeleton_orbits_and_farkas():
    orbs6 = pruner.enumerate_canonical_skeletons(6)
    assert len(orbs6) == 12, f"Expected 12 valid C6 orbits, got {len(orbs6)}"

    orbs5 = pruner.enumerate_canonical_skeletons(5)
    assert len(orbs5) == 97, f"Expected 97 valid C5 orbits, got {len(orbs5)}"

    if HAS_SCIPY:
        k44 = [15, 15, 15, 15]
        k44_minus_e = [14, 15, 15, 15]
        for name, sk in (("C5 K4,4", k44), ("C5 K4,4-e", k44_minus_e)):
            cert = pruner.find_farkas_certificate(5, sk)
            assert cert is not None, f"{name} should be Farkas-pruned!"
            y_eq, y_ub = cert
            assert pruner.verify_farkas_certificate(5, sk, y_eq, y_ub), f"{name} failed independent verifier"
            bad_ub = list(y_ub)
            bad_ub[0] = -1
            assert not pruner.verify_farkas_certificate(5, sk, y_eq, bad_ub), "Tampered negative y_ub accepted!"
            assert not pruner.verify_farkas_certificate(5, sk, [0] * len(y_eq), [0] * len(y_ub)), "Zero vector accepted!"

        circ3 = [((1 << i) | (1 << ((i + 1) % 6)) | (1 << ((i + 2) % 6))) for i in range(6)]
        cert3 = pruner.find_farkas_certificate(3, circ3)
        assert cert3 is not None and pruner.verify_farkas_certificate(3, circ3, *cert3)
    else:
        sparse_file = HERE / 'certificates' / 'd9c345_farkas_sparse.json'
        assert sparse_file.exists(), "Precomputed sparse certificates missing in non-scipy environment"
        bundle = json.loads(sparse_file.read_text())
        rec = bundle['cases']['C5']['pruned_certificates'][0]
        y_eq, y_ub = pruner.expand_sparse_farkas(5, rec['rows'], rec['y_eq_nz'], rec['y_ub_nz'])
        assert pruner.verify_farkas_certificate(5, rec['rows'], y_eq, y_ub)
        bad_ub = list(y_ub)
        bad_ub[0] = -1
        assert not pruner.verify_farkas_certificate(5, rec['rows'], y_eq, bad_ub)

    print("PASS [3/6]: Canonical skeleton enumeration (C6=12, C5=97) + exact Farkas & tamper tests", flush=True)


def test_compact_cnf_builders():
    sk_c5 = [1, 2, 4, 8]
    sk_c4 = [1, 2, 4, 8, 16]
    sk_c3 = [1, 2, 4, 8, 16, 32]
    for c, sk in ((5, sk_c5), (4, sk_c4), (3, sk_c3)):
        cnf, M, ET_var, meta = cnf_mod.build_d9c345_cnf(c, sk, adj_T=None)
        assert meta['mode'] == 'free_T'
        assert meta['nontrivial_t_pairs'] == 0
        assert len(M) == 18 - c and len(M[0]) == 20 + c
        assert len(ET_var) == (20 + c) * (19 + c)
        assert meta['vars'] > 0 and meta['clauses'] > 0

    sample_g6_27 = 'ZI_eD@@EOCG@dGO?OBGCeC?GRDC?gQW?yOCOI@a?gQCd@WOIGH_@g?L@oh??'
    adj27 = cnf_mod.decode_g6(sample_g6_27, expected_n=27)
    assert cnf_mod.encode_g6(adj27) == sample_g6_27
    cnf7, M7, ET7, meta7 = cnf_mod.build_d9c345_cnf(7, [3, 3], adj_T=adj27, include_i7=True)
    assert meta7['mode'] == 'fixed_core'
    assert meta7['i7_count'] == 750
    assert meta7['nontrivial_t_pairs'] == 0
    assert len(ET7) == 0

    print("PASS [4/6]: Compact CNF builders (Free-T for C5/C4/C3 + Fixed-Core I7/zero-redundant T-pairs)", flush=True)


def test_witness_verifier():
    empty = [0] * 40
    ok, reason = cnf_mod.verify_40_witness(empty, 5, check_alpha=False)
    assert not ok and 'non_9_regular' in reason

    k10x4 = [0] * 40
    for blk in range(4):
        base = blk * 10
        for i in range(10):
            for j in range(10):
                if i != j:
                    k10x4[base + i] |= 1 << (base + j)
    ok, reason = cnf_mod.verify_40_witness(k10x4, 5, check_alpha=False)
    assert not ok and 'triangle' in reason

    b20x2 = [0] * 40
    for blk in range(2):
        base = blk * 20
        for i in range(10):
            for j in range(10):
                if i != j:
                    u, v = base + i, base + 10 + j
                    b20x2[u] |= 1 << v
                    b20x2[v] |= 1 << u
    ok, reason = cnf_mod.verify_40_witness(b20x2, 5, check_alpha=True)
    assert not ok, "Disconnected 9-regular bipartite graph falsely accepted!"

    print("PASS [5/6]: Independent 40-vertex SAT witness verifier negative-control checks", flush=True)


def test_sharded_partition():
    cert_file = HERE / 'certificates' / 'd9c345_farkas_certificates.json'
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        if HAS_SCIPY:
            summary, _ = pruner.run_pruner(cases=(5,), out_dir=td_path)
            assert summary['cases']['C5']['surviving_orbits'] == 95
            assert summary['cases']['C5']['farkas_pruned_orbits'] == 2
            use_cert = td_path / 'd9c345_farkas_certificates.json'
            ver = pruner.verify_certificate_file(use_cert, td_path / 'd9c345_pruning_summary.json')
            assert ver['total_farkas_certs_verified'] == 2
        else:
            sparse_file = HERE / 'certificates' / 'd9c345_farkas_sparse.json'
            assert sparse_file.exists()
            ver = pruner.verify_sparse_certificate_file(sparse_file, HERE / 'certificates' / 'd9c345_pruning_summary.json')
            assert ver['total_farkas_certs_verified'] == 353
            use_cert = td_path / 'manifest_c5.json'
            pruner.build_surviving_manifest_stdlib(sparse_file, 'C5', use_cert)

        orbs = runner.load_surviving_orbits(use_cert, 'C5')
        assert len(orbs) == 95
        seen = set()
        for s in range(10):
            part = runner.assign_shard(orbs, s, 10)
            for o in part:
                assert o['id'] not in seen
                seen.add(o['id'])
        assert len(seen) == 95
        dry = runner.run_shard(use_cert, 'C5', 0, 10, td_path / 'shard0', dry_run=True)
        assert dry['shard_orbit_count'] == 10 and dry['dry_run'] is True

    print("PASS [6/6]: Sharded batch runner 10-shard disjoint full-coverage partition + dry-run", flush=True)


def main():
    t0 = time.monotonic()
    test_cnf_primitives()
    test_waterfill()
    test_skeleton_orbits_and_farkas()
    test_compact_cnf_builders()
    test_witness_verifier()
    test_sharded_partition()
    print(f"ALL 6/6 SELFTEST SUITES PASSED in {time.monotonic() - t0:.2f}s (scipy={HAS_SCIPY})", flush=True)


if __name__ == '__main__':
    main()
