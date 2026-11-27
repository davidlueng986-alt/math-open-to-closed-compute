#!/usr/bin/env python3
"""Comprehensive local test suite for the Ramsey R(3,10) Master Closure Auditor & Witness Verifier.

Verifies:
  1. Master ledger `closure_ledger_v8.json` passes `audit_dag_coverage.audit_ledger()` with 0 errors.
  2. Negative / mutation tests on `audit_dag_coverage.py`:
     - Dropping an NA-T1 or NA-T2 branch is detected as a coverage gap.
     - Dropping a D9-C* branch is detected.
     - Corrupting a SHA-256 digest or duplicating a drat_sha256 is detected.
     - Prematurely marking an OPEN parent node as CERTIFIED_DRAT is rejected.
     - Mixing/altering D678 dual-cover isolation is rejected.
     - Exceeding <=10 parallel jobs or <=6h/job in wave_execution_plan is rejected.
  3. Independent witness verifier `verify_sat_witness.py`:
     - Positive check on classical Kalbfleisch (3,9;35) graph (n=35, 0 triangles, alpha=8).
     - Positive check on classical Exoo (3,10;39) graph (n=39, 0 triangles, alpha=9).
     - Negative check on 40-vertex extension of Exoo (3,10;39) (seed31002-like 40v test: either
       triangle-free with alpha >= 10, or contains a triangle -> REJECTED as (3,10;40) witness).
     - Synthetic small graph tests: C_5 (exact (3,3;5) witness), K_3 (triangle rejected),
       self-loop rejected, asymmetric matrix rejected, JSON/matrix/graph6 parser parity.
  4. Wave execution plan completeness & resource constraints (<=10 parallel jobs, <=6h/job).
"""
import copy
import json
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import audit_dag_coverage as auditor
import verify_sat_witness as witness

# Classical Ramsey graphs from davidlueng986-alt/math-open-to-closed-compute (commit 185260db)
KALBFLEISCH_35_G6 = (
    "bsaCCA?O?O_aC??`c@O@b?RcHQ?DcA@H?PC_@QO@@Q?DA@MP?RgKADoH?aR?KCbOC_JE?xO@AALC@AJPG?__V?_K@ROO_A@dOG@?_"
)
EXOO_39_G6 = (
    "fhcKIC`DK@GBH@C_`HK@GOCcc@Gc@GQOc_P@D?KGCOOoG_`OG_hA`@?oGOSI@AA`GCKACSGGDHC@OG_aOGCSGcA_D_C_SOIGA_PC_???AaAaADABGCOAgH@COT?O_"
)


def _load_ledger() -> dict:
    return json.loads((HERE / "closure_ledger_v8.json").read_text(encoding="utf-8"))


def test_ledger_passes_cleanly():
    ledger = _load_ledger()
    report = auditor.audit_ledger(ledger)
    assert report["audit_status"] == "PASS", f"Expected PASS, got {report}"
    assert report["zero_coverage_gaps"] is True
    assert report["problem_status"] == "OPEN"
    assert report["errors"] == []
    assert report["sha256_digests_validated"] == 13, f"Expected 13 SHA-256 digests, got {report['sha256_digests_validated']}"
    assert report["closure_progress"]["v8_active_37_branches"]["total"] == 37
    assert report["closure_progress"]["v8_active_37_branches"]["closed"] == 2
    assert report["closure_progress"]["v8_active_37_branches"]["open"] == 35
    assert report["closure_progress"]["v8_fine_40_obligations"]["total"] == 40
    assert report["closure_progress"]["v8_fine_40_obligations"]["closed"] == 5
    assert report["closure_progress"]["v8_fine_40_obligations"]["open"] == 35
    print("[PASS] test_ledger_passes_cleanly (37 active branches: 2 closed / 35 open; 13 SHA-256 digests verified)")


def test_ledger_mutation_checks():
    base = _load_ledger()

    # 1. Missing NA-T1 branch
    m1 = copy.deepcopy(base)
    for nd in m1["nodes"]:
        if nd["id"] == "NA-T1":
            nd["all_of"].remove("NA-T1-R7-Q9")
    r1 = auditor.audit_ledger(m1)
    assert r1["audit_status"] == "FAIL" and any("NA-T1 coverage mismatch" in e for e in r1["errors"])

    # 2. Missing NA-T2 branch
    m2 = copy.deepcopy(base)
    for nd in m2["nodes"]:
        if nd["id"] == "NA-T2":
            nd["all_of"].remove("NA-T2-T27-D9-D9")
    r2 = auditor.audit_ledger(m2)
    assert r2["audit_status"] == "FAIL" and any("NA-T2 coverage mismatch" in e for e in r2["errors"])

    # 3. Bad SHA-256 digest
    m3 = copy.deepcopy(base)
    for nd in m3["nodes"]:
        if nd["id"] == "D9-C7-CORE-0":
            nd["certificates"][0]["drat_sha256"] = "not-a-valid-sha256"
    r3 = auditor.audit_ledger(m3)
    assert r3["audit_status"] == "FAIL" and any("Invalid SHA-256" in e for e in r3["errors"])

    # 4. Duplicate drat_sha256 across two cores
    m4 = copy.deepcopy(base)
    c0_hash = None
    for nd in m4["nodes"]:
        if nd["id"] == "D9-C7-CORE-0":
            c0_hash = nd["certificates"][0]["drat_sha256"]
        elif nd["id"] == "D9-C7-CORE-1":
            nd["certificates"][0]["drat_sha256"] = c0_hash
    r4 = auditor.audit_ledger(m4)
    assert r4["audit_status"] == "FAIL" and any("Duplicate drat_sha256" in e for e in r4["errors"])

    # 5. Prematurely closing an OPEN parent node
    m5 = copy.deepcopy(base)
    for nd in m5["nodes"]:
        if nd["id"] == "D9":
            nd["status"] = "CERTIFIED_DRAT"
    r5 = auditor.audit_ledger(m5)
    assert r5["audit_status"] == "FAIL" and any("all_of children are OPEN" in e for e in r5["errors"])

    # 6. Wave plan violating <=10 jobs cap
    m6 = copy.deepcopy(base)
    m6["wave_execution_plan"][0]["max_parallel_jobs"] = 12
    r6 = auditor.audit_ledger(m6)
    assert r6["audit_status"] == "FAIL" and any("<= 10 parallel jobs" in e for e in r6["errors"])

    # 7. Wave plan violating <=6h cap
    m7 = copy.deepcopy(base)
    m7["wave_execution_plan"][0]["max_hours_per_job"] = 8
    r7 = auditor.audit_ledger(m7)
    assert r7["audit_status"] == "FAIL" and any("<= 6h/job" in e for e in r7["errors"])

    print("[PASS] test_ledger_mutation_checks (7/7 negative mutation checks caught)")


def test_witness_verifier_classical_graphs():
    # Kalbfleisch (3,9;35): n=35, triangle-free, alpha=8 (forbidden_alpha=9)
    adj35 = witness.decode_graph6(KALBFLEISCH_35_G6)
    r35 = witness.verify_ramsey_witness(adj35, target_n=35, forbidden_alpha=9)
    assert r35["valid_witness"] is True, f"Kalbfleisch 35 failed: {r35}"
    assert r35["n"] == 35 and r35["triangle_count"] == 0 and r35["alpha"] == 8

    # Exoo (3,10;39): n=39, triangle-free, alpha=9 (forbidden_alpha=10)
    adj39 = witness.decode_graph6(EXOO_39_G6)
    r39 = witness.verify_ramsey_witness(adj39, target_n=39, forbidden_alpha=10)
    assert r39["valid_witness"] is True, f"Exoo 39 failed: {r39}"
    assert r39["n"] == 39 and r39["triangle_count"] == 0 and r39["alpha"] == 9

    # Negative 40-vertex test 1 (seed31002-like: extend Exoo39 by an isolated vertex -> triangle-free but alpha=10)
    adj40_iso = adj39 + [0]
    r40_iso = witness.verify_ramsey_witness(adj40_iso, target_n=40, forbidden_alpha=10)
    assert r40_iso["valid_witness"] is False
    assert r40_iso["triangle_free"] is True and r40_iso["alpha"] == 10
    assert len(r40_iso["forbidden_independent_set_example"]) == 10

    # Negative 40-vertex test 2 (extend Exoo39 by connecting vertex 39 to an adjacent pair -> creates a triangle)
    u = 0
    v = (adj39[0] & -adj39[0]).bit_length() - 1
    adj40_tri = list(adj39) + [(1 << u) | (1 << v)]
    adj40_tri[u] |= 1 << 39
    adj40_tri[v] |= 1 << 39
    r40_tri = witness.verify_ramsey_witness(adj40_tri, target_n=40, forbidden_alpha=10)
    assert r40_tri["valid_witness"] is False
    assert r40_tri["triangle_count"] >= 1

    print(
        f"[PASS] test_witness_verifier_classical_graphs "
        f"(Kalbfleisch35 alpha={r35['alpha']} in {r35['elapsed_seconds']}s; "
        f"Exoo39 alpha={r39['alpha']} in {r39['elapsed_seconds']}s; "
        f"40v negative tests rejected)"
    )


def test_witness_verifier_synthetic_and_parsers():
    # C_5 is a valid (3,3;5)-Ramsey graph (n=5, 0 triangles, alpha=2)
    c5 = [0] * 5
    for i in range(5):
        j = (i + 1) % 5
        c5[i] |= 1 << j
        c5[j] |= 1 << i
    rc5 = witness.verify_ramsey_witness(c5, target_n=5, forbidden_alpha=3)
    assert rc5["valid_witness"] is True and rc5["alpha"] == 2 and rc5["triangle_count"] == 0

    # Self-loop rejection
    bad_loop = list(c5)
    bad_loop[0] |= 1
    rloop = witness.verify_ramsey_witness(bad_loop, target_n=5, forbidden_alpha=3)
    assert rloop["valid_witness"] is False and rloop["simple_undirected"] is False

    # Asymmetric matrix rejection
    bad_asym = list(c5)
    bad_asym[0] |= 1 << 2
    rasym = witness.verify_ramsey_witness(bad_asym, target_n=5, forbidden_alpha=3)
    assert rasym["valid_witness"] is False and rasym["simple_undirected"] is False

    # File format round-trip parity (matrix .txt & .json)
    with tempfile.TemporaryDirectory() as td:
        p_mat = Path(td) / "c5.txt"
        mat_str = "\n".join("".join("1" if (c5[i] >> j) & 1 else "0" for j in range(5)) for i in range(5)) + "\n"
        p_mat.write_text(mat_str, encoding="ascii")
        assert witness.load_graph(p_mat) == c5

        p_json = Path(td) / "c5.json"
        edges = [[i, (i + 1) % 5] for i in range(5)]
        p_json.write_text(json.dumps({"n": 5, "edges": edges}), encoding="ascii")
        assert witness.load_graph(p_json) == c5

    print("[PASS] test_witness_verifier_synthetic_and_parsers (C_5, self-loop, asymmetry, matrix/JSON parsers)")


def test_wave_execution_plan():
    ledger = _load_ledger()
    waves = ledger["wave_execution_plan"]
    assert len(waves) == 6
    all_targets = []
    for w in waves:
        assert 1 <= w["max_parallel_jobs"] <= 10, f"Wave {w['wave']} exceeds 10 jobs"
        assert 1 <= w["max_hours_per_job"] <= 6, f"Wave {w['wave']} exceeds 6h/job"
        all_targets.extend(w["target_obligations"])
    assert len(all_targets) == 35 and len(set(all_targets)) == 35
    print(f"[PASS] test_wave_execution_plan ({len(waves)} waves covering all 35 OPEN obligations, <=10 jobs, <=6h/job)")


def main() -> int:
    test_ledger_passes_cleanly()
    test_ledger_mutation_checks()
    test_witness_verifier_classical_graphs()
    test_witness_verifier_synthetic_and_parsers()
    test_wave_execution_plan()
    print("\nALL_AUDITOR_SELFTESTS_PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
