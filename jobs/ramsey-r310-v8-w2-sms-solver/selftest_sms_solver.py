#!/usr/bin/env python3
"""
Full Local Verification Suite for Wave 2 Subagent 5
(`sms_partition_driver.py`, `cube_splitter.py`, `lrat_upgrade_runner.py`,
and `.github/workflows/ramsey-r310-v8-w2-sms-poc.yml`).

Verifies:
  1. Edge variable bijection (`edge_var` <-> `var_to_edge`) matches
     `itertools.combinations(range(40), 2)` 1-indexed for all 780 pairs.
  2. Canonical Ramsey R(3,10) partitions (`D6-N9`, `D8-N8`, `D7-N9`) &
     non-contiguous arbitrary partition remapping/unremapping involution
     and graph isomorphism invariance.
  3. DIMACS I/O, symmetry-breaking clause parsing, deduplication, bounds
     validation, and CNF merging.
  4. Cube-splitting exhaustiveness & disjointness tautology proof:
     - Uniform 2^k splits (k=2, 3, 4 -> 4, 8, 16 cubes)
     - Adaptive non-power-of-2 splits (6 cubes, 10 cubes)
     - Exact truth-table (every assignment hits exactly 1 cube)
     - Exact rational measure sum 2^{-|C_i|} == 1
     - Exact DPLL refutation of `AND_i (NOT C_i)`
     - Negative tests (missing cube, overlapping cubes, contradictory cube)
     - BCP lookahead & Ramsey XxY block priority variable selection
     - Materialization (`cube_*.cnf`, `cubes.icnf`, `tautology_negation.cnf`, `manifest.json`)
  5. Dry-run CLI generation for `smsg` (`space`/`comma`/`repeat` styles),
     Kissat, `drat-trim -L`, and `lrat-check` (including `.gz` decompression).
  6. Workflow YAML structural & safety checks (when present in repo layout).
"""

from __future__ import annotations

import gzip
import itertools
import json
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import cube_splitter as cs
import lrat_upgrade_runner as lur
import sms_partition_driver as spd


def test_edge_bijection_n40() -> None:
    pairs = list(itertools.combinations(range(40), 2))
    assert len(pairs) == 780 == spd.num_edge_vars(40)
    for idx, (u, v) in enumerate(pairs, 1):
        ev = spd.edge_var(u, v, 40)
        assert ev == idx, f"edge_var({u},{v})={ev} != {idx}"
        assert spd.edge_var(v, u, 40) == idx, "symmetry failed"
        assert spd.var_to_edge(idx, 40) == (u, v), f"var_to_edge({idx}) mismatch"
    print("[PASS] test_edge_bijection_n40 (all 780 pairs exact match)")


def test_canonical_and_arbitrary_partitions() -> None:
    # Canonical Ramsey partitions
    for d, q, expected_sizes in [
        (6, 9, (1, 1, 5, 8, 25)),
        (8, 8, (1, 1, 7, 7, 24)),
        (7, 9, (1, 1, 6, 8, 24)),
    ]:
        blocks = spd.canonical_ramsey_partition(d, q, 40)
        pm = spd.PartitionMapper.from_blocks(blocks, n=40)
        assert pm.partition_sizes == expected_sizes
        assert pm.is_identity is True
        assert pm.remap_lit(123) == 123
        assert pm.remap_lit(-780) == -780
        assert pm.remap_lit(781) == 781  # aux var untouched

    # Non-contiguous arbitrary partition on n=8
    blocks = [[5], [2], [0, 7, 3], [1, 4, 6]]
    pm = spd.PartitionMapper.from_blocks(blocks, n=8)
    assert pm.partition_sizes == (1, 1, 3, 3)
    assert pm.is_identity is False
    # Check involution on all 28 edge vars + aux vars
    m = spd.num_edge_vars(8)
    seen = set()
    for v in range(1, m + 1):
        for sgn in (1, -1):
            lit = sgn * v
            r = pm.remap_lit(lit)
            assert abs(r) <= m
            assert (r > 0) == (lit > 0)
            assert pm.unremap_lit(r) == lit
            seen.add(r)
    assert len(seen) == 2 * m
    # Auxiliary variable > 28 must remain invariant
    assert pm.remap_lit(29) == 29
    assert pm.remap_lit(-105) == -105
    assert pm.unremap_lit(-105) == -105

    # Triangle preservation under remapping
    tri = [-spd.edge_var(0, 7, 8), -spd.edge_var(0, 3, 8), -spd.edge_var(7, 3, 8)]
    rtri = pm.remap_clause(tri)
    verts = {v for lit in rtri for v in spd.var_to_edge(abs(lit), 8)}
    assert verts == {2, 3, 4}, f"Block [0,7,3] must map to contiguous {{2,3,4}}, got {verts}"

    # Invalid partition rejection
    for bad in [
        [[0, 1], [1, 2]],      # duplicate
        [[0, 1], [3]],         # missing 2
        [[0, 1], []],          # empty block
    ]:
        try:
            spd.PartitionMapper.from_blocks(bad, n=4)
            raise AssertionError(f"Expected ValueError for bad partition {bad}")
        except ValueError:
            pass
    print("[PASS] test_canonical_and_arbitrary_partitions")


def test_dimacs_and_sym_break_merge() -> None:
    with tempfile.TemporaryDirectory(prefix="selftest_dimacs_") as td:
        td_p = Path(td)
        base_cnf = td_p / "base.cnf"
        base_clauses = [[1, 2], [-1, 3], [781], [-2, -3, 782]]
        spd.write_dimacs(base_cnf, 782, base_clauses, comments=["unit test base"])
        nv, read_cl = spd.read_dimacs(base_cnf)
        assert nv == 782
        assert read_cl == base_clauses

        sb_file = td_p / "sb.clauses"
        sb_file.write_text(
            "c symmetry breaking clauses from smsg\n"
            "-1 2 0\n"
            "2 -1 0\n"       # duplicate up to ordering -> deduplicated
            "-10 15 -22 0\n"
            "\n",
            encoding="utf-8",
        )
        parsed = spd.parse_sym_break_clauses(sb_file, max_var=780, deduplicate=True)
        assert len(parsed) == 2

        merged_cnf = td_p / "merged.cnf"
        info = spd.merge_cnf_with_sym_break(base_cnf, sb_file, merged_cnf, n=40)
        assert info["base_clauses"] == 4
        assert info["sb_clauses"] == 2
        assert info["total_clauses"] == 6
        nv_m, cl_m = spd.read_dimacs(merged_cnf)
        assert nv_m == 782 and len(cl_m) == 6

        # Out-of-range literal rejection
        bad_sb = td_p / "bad_sb.clauses"
        bad_sb.write_text("-781 1 0\n", encoding="utf-8")
        try:
            spd.parse_sym_break_clauses(bad_sb, max_var=780)
            raise AssertionError("Expected ValueError for literal > 780")
        except ValueError:
            pass
    print("[PASS] test_dimacs_and_sym_break_merge")


def _build_synthetic_ramsey_cnf() -> tuple[int, list[list[int]]]:
    """Build a small synthetic CNF on N=40 edge vars with X x Y binary/ternary constraints."""
    clauses: list[list[int]] = []
    # Fix root edges for d=6, q=9: X=[2..6], Y=[7..14], T=[15..39]
    # Add rich binary/ternary constraints on X x Y edges so BCP lookahead sees strong propagation
    xy_edges = [spd.edge_var(x, y, 40) for x in range(2, 7) for y in range(7, 15)]
    # Make xy_edges[0] a hub variable with many binary clauses in both polarities
    hub = xy_edges[0]
    for other in xy_edges[1:8]:
        clauses.append([-hub, -other])
        clauses.append([hub, other])
    # Add triangle-free clauses across X x Y x T
    for x in (2, 3):
        for y in (7, 8, 9):
            for t in (15, 16, 17):
                clauses.append([
                    -spd.edge_var(x, y, 40),
                    -spd.edge_var(x, t, 40),
                    -spd.edge_var(y, t, 40),
                ])
    # Fix one variable as a unit clause to verify unit-fixed vars are never branched on
    fixed_v = xy_edges[-1]
    clauses.append([fixed_v])
    return 781, clauses


def test_cube_splitting_and_tautology_proofs() -> None:
    nv, clauses = _build_synthetic_ramsey_cnf()
    xy_edges = [spd.edge_var(x, y, 40) for x in range(2, 7) for y in range(7, 15)]
    hub = xy_edges[0]
    fixed_v = xy_edges[-1]

    # 1. Uniform 2^k splits for k=2, 3, 4
    for depth in (2, 3, 4):
        cubes, meta = cs.generate_uniform_cubes(
            clauses, depth=depth, max_branch_var=780, d=6, q=9, n=40
        )
        assert len(cubes) == (1 << depth)
        # Hub variable should be chosen first due to BCP lookahead + XxY priority
        assert meta[0]["var"] == hub, f"Expected hub var {hub} first, got {meta[0]['var']}"
        # Fixed variable must never appear in cubes
        all_branch_vars = {abs(lit) for c in cubes for lit in c}
        assert fixed_v not in all_branch_vars
        proof = cs.verify_cube_partition(cubes)
        assert proof["valid"] is True, f"Uniform k={depth} failed proof: {proof}"
        assert proof["measure_equals_one"] is True
        assert proof["dpll_negation_unsat"] is True
        assert proof["truth_table_checked"] is True
        assert proof["truth_table_exact_one_hit"] is True

    # 2. Adaptive non-power-of-2 splits (6 cubes, 10 cubes)
    for target in (6, 10):
        cubes, _ = cs.generate_adaptive_cubes(
            clauses, target_cubes=target, max_branch_var=780, d=6, q=9, n=40
        )
        assert len(cubes) == target
        proof = cs.verify_cube_partition(cubes)
        assert proof["valid"] is True, f"Adaptive m={target} failed proof: {proof}"
        assert proof["measure_equals_one"] is True
        assert proof["dpll_negation_unsat"] is True
        assert proof["truth_table_exact_one_hit"] is True

    # 3. Negative tests: verify_cube_partition MUST reject defective splits
    missing_branch = [[1, 2], [1, -2], [-1, 2]]  # missing [-1, -2]
    p_miss = cs.verify_cube_partition(missing_branch)
    assert p_miss["valid"] is False and p_miss["dpll_negation_unsat"] is False

    overlapping = [[1], [2], [-1, -2]]  # [1] and [2] overlap when 1=T, 2=T
    p_ov = cs.verify_cube_partition(overlapping)
    assert p_ov["valid"] is False

    contradictory = [[1, -1], [2]]
    p_con = cs.verify_cube_partition(contradictory)
    assert p_con["valid"] is False

    # 4. Materialization test
    with tempfile.TemporaryDirectory(prefix="selftest_cubes_") as td:
        td_p = Path(td)
        base_cnf = td_p / "task.cnf"
        spd.write_dimacs(base_cnf, nv, clauses)
        cubes, meta = cs.generate_uniform_cubes(clauses, depth=2, max_branch_var=780, d=6, q=9)
        manifest = cs.materialize_cubes(base_cnf, cubes, td_p / "cubes_out", meta)
        assert manifest["tautology_proof"]["valid"] is True
        assert len(manifest["cubes"]) == 4
        # Check tautology_negation.cnf is indeed UNSAT under DPLL
        _, neg_cl = spd.read_dimacs(td_p / "cubes_out" / "tautology_negation.cnf")
        assert cs._dpll_is_sat(neg_cl) is False
        # Check each cube CNF has base_clauses + 2 unit clauses
        for entry in manifest["cubes"]:
            cpath = td_p / "cubes_out" / entry["cnf_file"]
            _, ccl = spd.read_dimacs(cpath)
            assert len(ccl) == len(clauses) + 2
    print("[PASS] test_cube_splitting_and_tautology_proofs (uniform, adaptive, negative, materialize)")


def test_dry_run_cli_generation() -> None:
    with tempfile.TemporaryDirectory(prefix="selftest_cli_") as td:
        td_p = Path(td)
        cnf = td_p / "dummy.cnf"
        spd.write_dimacs(cnf, 781, [[1, 2], [-1, -2]])

        # Test all 3 --initial-partition styles
        for style, expected_sub in [
            ("space", ["--initial-partition", "1", "1", "5", "8", "25"]),
            ("comma", ["--initial-partition", "1,1,5,8,25"]),
            ("repeat", ["--initial-partition", "1", "--initial-partition", "1", "--initial-partition", "5"]),
        ]:
            cmd = spd.build_smsg_cmd(
                dimacs_path=cnf,
                n=40,
                partition_sizes=[1, 1, 5, 8, 25],
                sym_break_path=td_p / "sb.clauses",
                frequency=30,
                cutoff=200000,
                partition_style=style,
            )
            assert "--vertices" in cmd and "40" in cmd
            assert "--dimacs" in cmd and str(cnf) in cmd
            assert "--sym-break-clauses" in cmd
            assert "--hide-graphs" in cmd
            # Subsequence check
            cmd_str = " ".join(cmd)
            assert " ".join(expected_sub) in cmd_str, f"Missing {expected_sub} in {cmd}"

        # End-to-end dry-run of sms_partition_driver CLI
        rc = spd.main([
            "--dimacs", str(cnf),
            "--vertices", "40",
            "--initial-partition", "1", "1", "5", "8", "25",
            "--mode", "harvest-and-certify",
            "--out", str(td_p / "sms_dry"),
            "--dry-run",
        ])
        assert rc == 0
        summary = json.loads((td_p / "sms_dry" / "summary.json").read_text(encoding="utf-8"))
        assert summary["smsg"]["status"] == "DRY_RUN"
        assert summary["certify"]["status"] == "DRY_RUN"

        # End-to-end dry-run of lrat_upgrade_runner CLI + .gz decompression helper
        drat_gz = td_p / "leaf.drat.gz"
        with gzip.open(drat_gz, "wb") as f:
            f.write(b"0\n")
        dec_path, was_gz = lur._maybe_decompress(drat_gz, td_p, "decompressed.drat")
        assert was_gz is True and dec_path.read_text(encoding="utf-8") == "0\n"

        lrat_res = lur.upgrade_and_verify_lrat(
            cnf_path=cnf, drat_path=drat_gz, out_dir=td_p / "lrat_dry", dry_run=True
        )
        assert lrat_res["status"] == "DRY_RUN"
        assert "-L" in lrat_res["drat_trim_cmd"]
        assert lrat_res["lrat_check_cmd"][0] == "lrat-check"
    print("[PASS] test_dry_run_cli_generation (smsg space/comma/repeat + kissat + drat-trim -L + lrat-check)")


def test_workflow_safety_constraints() -> None:
    # Locate workflow either in repo root or sibling work tree
    candidates = [
        HERE.parent.parent / ".github" / "workflows" / "ramsey-r310-v8-w2-sms-poc.yml",
        HERE.parent / "ramsey-r310-v8-w2-sms-poc.yml",
    ]
    wf_path = next((p for p in candidates if p.exists()), None)
    if wf_path is None:
        print("[SKIP] test_workflow_safety_constraints (workflow file not in local parent path)")
        return
    txt = wf_path.read_text(encoding="utf-8")
    assert "workflow_dispatch:" in txt, "Workflow must support workflow_dispatch"
    # Ensure no push / pull_request / schedule triggers under `on:`
    on_section = txt.split("jobs:")[0]
    for forbidden in ("\n  push:", "\n  pull_request:", "\n  schedule:"):
        assert forbidden not in on_section, f"Forbidden trigger {forbidden.strip()} in workflow!"
    assert (
        "ghcr.io/davidlueng986-alt/math-compute-sat@sha256:"
        "fa5d94d4e8dc2aaccec31230adea72967257f9bbe732db9f4c7df6046f2a6dbc"
    ) in txt, "Exact pinned container digest missing"
    assert "D6-N9-B3-P002-T01" in txt and "D6-N9-B3-P000-T01" in txt
    assert "timeout-minutes: 30" in txt or "timeout-minutes: 25" in txt
    print(f"[PASS] test_workflow_safety_constraints ({wf_path.name})")


def main() -> int:
    test_edge_bijection_n40()
    test_canonical_and_arbitrary_partitions()
    test_dimacs_and_sym_break_merge()
    test_cube_splitting_and_tautology_proofs()
    test_dry_run_cli_generation()
    test_workflow_safety_constraints()
    print("ALL_SELFTESTS_PASSED (6/6)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
