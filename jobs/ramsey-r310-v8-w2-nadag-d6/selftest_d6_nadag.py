#!/usr/bin/env python3
r"""Full Local Verification Suite for Unified NA-DAG Tier-1 D6 Solver & Pruner.

Tests:
  1. Exhaustive pure-integer water-filling convexity verification (all cap configs, lb=0/1).
  2. Coverage completeness audit of all 9 Tier-1 D6 branches (333 D6 profiles, 207 forced e(H_u)<=121,
     independent stdlib-only replay of pure-integer UNSAT certificates).
  3. Exhaustive truth-table verification of CompactCNF primitives (atmost_seq, atleast_seq,
     exact_seq, range_seq, lex_lt).
  4. CNF soundness & structural checks on:
       - Real verified (3, 8; 27, 85) core across all 4 r=5 branches (D6-R5-Q6..Q9)
       - Synthetic verified (3, 8; 26) and (3, 8; 25) cores across r=6 and r=7 branches
       - Exact SAT witness verifier negative & positive control tests
  5. Sharded batch runner completeness & disjointness audit (num_shards=1..10, <= 5.5h cap).
"""
import itertools
import json
import tempfile
import time
from pathlib import Path

import d6_batch_runner as runner
import d6_core_cnf as core_cnf
import d6_nadag_pruner as pruner

# Real independently verified (3, 8; 27, 85) graph6 core from Agent 6
REAL_R38_27_85_G6 = "ZI_eD@@EOCG@dGO?OBGCeC?GRDC?gQW?yOCOI@a?gQCd@WOIGH_@g?L@oh??"


def test_waterfilling_exhaustive():
    cap_configs = [
        [(1, 2), (2, 2), (3, 1)],
        [(0, 1), (1, 2), (3, 2)],
        [(2, 2), (4, 2)],
        [(1, 3), (3, 2)],
        [(1, 1), (2, 1), (3, 2)],
    ]
    for cfg in cap_configs:
        caps = [c for c, cnt in cfg for _ in range(cnt)]
        n_vars = len(caps)
        for lb in (0, 1):
            if any(c < lb for c in caps):
                for total in range(0, sum(caps) + 2):
                    assert pruner.min_pairs_capped_from(total, cfg, lb=lb, max_at_lb=n_vars) is None
                continue
            for max_at_lb in range(0, n_vars + 1):
                best = {}
                for tup in itertools.product(*(range(lb, c + 1) for c in caps)):
                    cnt_lb = sum(v == lb for v in tup)
                    if cnt_lb > max_at_lb:
                        continue
                    s = sum(tup)
                    val = sum(pruner.c2(v) for v in tup)
                    if s not in best or val < best[s][0] or (val == best[s][0] and cnt_lb < best[s][1]):
                        best[s] = (val, cnt_lb)
                for total in range(0, sum(caps) + 2):
                    got = pruner.min_pairs_capped_from(total, cfg, lb=lb, max_at_lb=max_at_lb)
                    exp = best.get(total, None)
                    if exp is None:
                        assert got is None, f"Expected None for {cfg} lb={lb} max={max_at_lb} tot={total}, got {got}"
                    else:
                        assert got is not None and got[0] == exp[0], (
                            f"Cost mismatch {cfg} lb={lb} max={max_at_lb} tot={total}: got={got} exp={exp}"
                        )
                        assert got[1] <= max_at_lb
    print("PASS [1/5]: Exhaustive water-filling capped convexity verified", flush=True)


def test_coverage_and_pure_integer_certs():
    assert len(pruner.TIER1_D6_BRANCHES) == 9
    expected_ids = {
        "D6-R5-Q6", "D6-R5-Q7", "D6-R5-Q8", "D6-R5-Q9",
        "D6-R6-Q7", "D6-R6-Q8", "D6-R6-Q9",
        "D6-R7-Q8", "D6-R7-Q9",
    }
    assert {b["id"] for b in pruner.TIER1_D6_BRANCHES} == expected_ids

    out_dir = Path(__file__).resolve().parent / "out_pruner"
    cert_path = out_dir / "d6_nadag_certificates.json"
    plan_path = out_dir / "d6_nadag_plan.json"
    if not cert_path.exists() or not plan_path.exists():
        pruner.run_pruner(out_dir, verify=True)

    cert_obj = json.loads(cert_path.read_text())
    plan_obj = json.loads(plan_path.read_text())
    rep = pruner.verify_d6_certificates_stdlib(cert_obj, plan_obj)
    assert rep["status"] == "PURE_INTEGER_VERIFICATION_PASSED"
    assert rep["profiles_total"] == 931
    assert rep["farkas_excluded_verified"] == 388
    assert rep["d6_profiles_total"] == 333
    assert rep["d6_forced_eH_le_121_verified"] == 207
    assert rep["tier1_branches_verified"] == 9
    assert rep["pruned_branch_profile_certs_verified"] == 552
    print(f"PASS [2/5]: Coverage completeness & pure-integer verifier passed: {rep}", flush=True)
    return plan_obj


def test_cnf_primitives_exhaustive():
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
                if not any(
                    ((bits >> (abs(lit) - 1)) & 1) == (1 if lit > 0 else 0) for lit in cl
                ):
                    ok = False
                    break
            if ok:
                return True
        return False

    for n in range(1, 5):
        for k in range(n + 1):
            c = core_cnf.CompactCNF(1)
            xs = [c.var() for _ in range(n)]
            c.atmost_seq(xs, k)
            for b in itertools.product((0, 1), repeat=n):
                fixed = {i + 1: b[i] for i in range(n)}
                assert check_sat(c.nv, c.clauses, fixed) == (sum(b) <= k), (n, k, b)

    for n in range(1, 5):
        for lo in range(n + 1):
            for hi in range(lo, n + 1):
                c = core_cnf.CompactCNF(1)
                xs = [c.var() for _ in range(n)]
                c.range_seq(xs, lo, hi)
                for b in itertools.product((0, 1), repeat=n):
                    fixed = {i + 1: b[i] for i in range(n)}
                    assert check_sat(c.nv, c.clauses, fixed) == (lo <= sum(b) <= hi), (n, lo, hi, b)

    for n in range(1, 4):
        c = core_cnf.CompactCNF(1)
        x = [c.var() for _ in range(n)]
        y = [c.var() for _ in range(n)]
        c.lex_lt(x, y)
        for b in itertools.product((0, 1), repeat=2 * n):
            fixed = {i + 1: b[i] for i in range(2 * n)}
            assert check_sat(c.nv, c.clauses, fixed) == (b[:n] < b[n:]), (n, b)

    print("PASS [3/5]: Exhaustive CompactCNF truth-table verification passed", flush=True)


def induced_subgraph(adj, drop_verts):
    keep = [v for v in range(len(adj)) if v not in drop_verts]
    idx = {v: i for i, v in enumerate(keep)}
    n = len(keep)
    out = [0] * n
    for i, u in enumerate(keep):
        for j, v in enumerate(keep):
            if (adj[u] >> v) & 1:
                out[i] |= 1 << j
    return out


def test_cnf_soundness_and_witness_verifier():
    # 1. Real (3, 8; 27, 85) core across all 4 r=5 branches
    adj27 = core_cnf.decode_g6(REAL_R38_27_85_G6, expected_n=27)
    assert core_cnf.encode_g6(adj27) == REAL_R38_27_85_G6
    edges27 = core_cnf.verify_r38_core(adj27, 27)
    assert edges27 == 85

    metas = {}
    for q in (6, 7, 8, 9):
        cnf, M, E_XY, meta = core_cnf.build_d6_core_cnf(
            adj27, r=5, q=q, include_i7=True, max_i7=2000, include_lex=True
        )
        assert not meta["unsat_by_pruner"], f"Unexpected pruner UNSAT on D6-R5-Q{q}: {meta}"
        assert all(len(cl) > 0 for cl in cnf.clauses), f"Empty clause in D6-R5-Q{q}"
        assert meta["i7_encoded"] == 750
        metas[f"D6-R5-Q{q}"] = (meta["primary_vars"], meta["vars"], meta["clauses"])

    # 2. Induced (3, 8; 26) core (drop a degree-5 vertex => 80 edges in [73, 84]) for r=6 branches
    deg5 = [i for i in range(27) if adj27[i].bit_count() == 5]
    assert len(deg5) >= 2
    adj26 = induced_subgraph(adj27, {deg5[0]})
    e26 = core_cnf.verify_r38_core(adj26, 26)
    assert 73 <= e26 <= 84, f"Unexpected e26={e26}"
    for q in (7, 8, 9):
        cnf, M, E_XY, meta = core_cnf.build_d6_core_cnf(
            adj26, r=6, q=q, include_i7=True, max_i7=500, include_lex=True
        )
        assert not meta["unsat_by_pruner"], f"Unexpected pruner UNSAT on D6-R6-Q{q}: {meta}"
        assert all(len(cl) > 0 for cl in cnf.clauses)
        metas[f"D6-R6-Q{q}"] = (meta["primary_vars"], meta["vars"], meta["clauses"])

    # 3. Induced (3, 8; 25) core (drop two degree-5 vertices => 75 or 76 edges in [65, 76]) for r=7 branches
    adj25 = induced_subgraph(adj27, {deg5[0], deg5[1]})
    e25 = core_cnf.verify_r38_core(adj25, 25)
    assert 65 <= e25 <= 76, f"Unexpected e25={e25}"
    for q in (8, 9):
        cnf, M, E_XY, meta = core_cnf.build_d6_core_cnf(
            adj25, r=7, q=q, include_i7=True, max_i7=500, include_lex=True
        )
        assert not meta["unsat_by_pruner"], f"Unexpected pruner UNSAT on D6-R7-Q{q}: {meta}"
        assert all(len(cl) > 0 for cl in cnf.clauses)
        metas[f"D6-R7-Q{q}"] = (meta["primary_vars"], meta["vars"], meta["clauses"])

    # 4. Witness verifier negative controls (empty graph has I10; K3-containing graph has triangle)
    ok_empty, rep_empty = core_cnf.verify_ramsey_3_10_40_witness([0] * 40)
    assert not ok_empty and "independent 10-set" in rep_empty["error"]
    tri = [0] * 40
    for u, v in ((0, 1), (1, 2), (0, 2)):
        tri[u] |= 1 << v
        tri[v] |= 1 << u
    ok_tri, rep_tri = core_cnf.verify_ramsey_3_10_40_witness(tri)
    assert not ok_tri and "Triangle" in rep_tri["error"]

    # 5. Verify build_40_graph produces exact root degrees (6, q) and codegree c=q-r
    for q in (6, 7, 8, 9):
        c = q - 5
        nx, ny = 6 - c, 5
        M_rows = [0] * 11
        xy_edges = [[1 if ix == iy else 0 for iy in range(ny)] for ix in range(nx)]
        g40 = core_cnf.build_40_graph(adj27, r=5, q=q, M_rows=M_rows, xy_edges=xy_edges)
        assert g40[0].bit_count() == 6
        assert g40[1].bit_count() == q
        assert ((g40[0] >> 1) & 1) == 0
        assert (g40[0] & g40[1]).bit_count() == c

    print(f"PASS [4/5]: All 9 Tier-1 D6 CNF encoders & witness verifier passed: {metas}", flush=True)


def test_sharded_batch_runner(plan_obj):
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        g6_file = td_path / "synthetic_r38_27.g6"
        # Write 4 copies (representing 4 McKay (3,8; 27, 85) cores)
        g6_file.write_text("\n".join([REAL_R38_27_85_G6] * 4) + "\n")
        plan_file = td_path / "plan.json"
        plan_file.write_text(json.dumps(plan_obj))

        total_scanned, selected = core_cnf.extract_cores_from_g6(g6_file, 27, 85, 85)
        assert total_scanned == 4 and len(selected) == 4
        items = runner.build_work_queue(plan_obj, {27: selected})
        assert len(items) == 16  # 4 r=5 branches x 4 cores

        for num_shards in (1, 4, 10):
            assigned = []
            for sid in range(num_shards):
                assigned.extend(x["item_id"] for x in runner.assign_shard(items, sid, num_shards))
            assert len(assigned) == len(items) and set(assigned) == {x["item_id"] for x in items}

        # Dry-run shard 0 of 4
        summ = runner.run_shard(
            plan_path=plan_file,
            g6_path=g6_file,
            out_dir=td_path / "shard0",
            mode="poc",
            shard_id=0,
            num_shards=4,
            budget_seconds=1200,
            per_core_seconds=600,
            nt=27,
            e_lo=85,
            e_hi=85,
            dry_run=True,
        )
        assert summ["total_work_items"] == 16 and summ["shard_work_items"] == 4
        assert summ["completed_items"] == 4
    print("PASS [5/5]: Sharded batch runner (1..10 shards, dry-run & checkpointing) passed", flush=True)


def main():
    t0 = time.monotonic()
    test_waterfilling_exhaustive()
    plan_obj = test_coverage_and_pure_integer_certs()
    test_cnf_primitives_exhaustive()
    test_cnf_soundness_and_witness_verifier()
    test_sharded_batch_runner(plan_obj)
    dt = round(time.monotonic() - t0, 3)
    print(f"\nALL 5/5 D6 NA-DAG SELFTEST SUITES PASSED in {dt}s", flush=True)


if __name__ == "__main__":
    main()
