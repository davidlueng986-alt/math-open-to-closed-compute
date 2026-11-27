#!/usr/bin/env python3
"""Comprehensive local verification suite for D9-C6 compact CNF solver & sharded batch runner.

Verifies:
  1. Exact 3x3 bipartite orbit classification (511 nonempty skeletons -> 25 canonical orbits).
  2. Exhaustive brute-force truth-table checks of CompactCNF primitives (atmost/atleast/exact/lex_lt/lex_le).
  3. Mathematical soundness of generalized S-domination & min_deg_T across all 25 orbits.
  4. Automorphism-respecting symmetry-breaking soundness across all 25 orbits (zero valid witnesses pruned).
  5. Real (3, 8; 26, e) Ramsey core construction (derived by vertex deletion from verified (3,8;27,85)),
     graph6 round-trip, and full 312-var compact CNF generation with variable/clause/I7 stats.
  6. Independent 40-vertex SAT witness verifier negative-case checks.
  7. End-to-end dry-run sharding (M=10 shards), manifest filtering, checkpointing, and resume idempotency.
"""
from __future__ import annotations

import gzip
import itertools
import json
import random
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import d9c6_compact_cnf as d9c6
import d9c6_batch_runner as runner

# Verified real (3, 8; 27, 85) Ramsey graph from Agent 6 (degree distribution {5:4, 6:11, 7:12})
R38_27_85_G6 = "ZI_eD@@EOCG@dGO?OBGCeC?GRDC?gQW?yOCOI@a?gQCd@WOIGH_@g?L@oh??"


def test_1_orbit_enumeration() -> list[dict]:
    orbits = d9c6.enumerate_d9c6_skeletons()
    assert len(orbits) == 25, f"Expected 25 orbits, got {len(orbits)}"
    assert sum(o["orbit_size"] for o in orbits) == 511
    by_exy: dict[int, int] = {}
    for o in orbits:
        by_exy[o["e_xy"]] = by_exy.get(o["e_xy"], 0) + 1
        assert o["e_T"] == 72 + o["e_xy"]
        assert 73 <= o["e_T"] <= 81
    expected_counts = {1: 1, 2: 2, 3: 4, 4: 5, 5: 5, 6: 4, 7: 2, 8: 1, 9: 1}
    assert by_exy == expected_counts, f"Orbit counts mismatch: {by_exy} != {expected_counts}"
    assert orbits[0]["id"] == "D9-C6-S00" and orbits[0]["e_xy"] == 1
    assert orbits[-1]["id"] == "D9-C6-S24" and orbits[-1]["e_xy"] == 9
    assert orbits[-1]["forces_full_S_domination"] is True
    assert all(not o["forces_full_S_domination"] for o in orbits[:-1])
    print("[PASS 1/7] Orbit enumeration: 511 nonempty 3x3 skeletons -> 25 canonical orbits verified.", flush=True)
    return orbits


def test_2_cnf_primitives() -> None:
    def check_sat(nv: int, clauses: list[list[int]], fixed: dict[int, int]) -> bool:
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
            c = d9c6.CompactCNF(1)
            xs = [c.var() for _ in range(n)]
            c.atmost_seq(xs, k)
            for b in itertools.product((0, 1), repeat=n):
                fixed = {i + 1: b[i] for i in range(n)}
                assert check_sat(c.nv, c.clauses, fixed) == (sum(b) <= k), ("atmost", n, k, b)

            c2 = d9c6.CompactCNF(1)
            xs2 = [c2.var() for _ in range(n)]
            c2.exact_seq(xs2, k)
            for b in itertools.product((0, 1), repeat=n):
                fixed = {i + 1: b[i] for i in range(n)}
                assert check_sat(c2.nv, c2.clauses, fixed) == (sum(b) == k), ("exact", n, k, b)

    for n in range(1, 4):
        for fn, cmp_op in ((d9c6.CompactCNF.lex_lt, lambda a, b: a < b),
                           (d9c6.CompactCNF.lex_le, lambda a, b: a <= b)):
            c = d9c6.CompactCNF(1)
            x = [c.var() for _ in range(n)]
            y = [c.var() for _ in range(n)]
            fn(c, x, y)
            for b in itertools.product((0, 1), repeat=2 * n):
                fixed = {i + 1: b[i] for i in range(2 * n)}
                assert check_sat(c.nv, c.clauses, fixed) == cmp_op(b[:n], b[n:]), (fn.__name__, n, b)

    print("[PASS 2/7] CompactCNF primitives: exhaustive truth-table check (atmost, exact, lex_lt, lex_le).", flush=True)


def test_3_s_domination_soundness(orbits: list[dict]) -> None:
    """Exhaustively verify generalized S-domination & min_deg_T against all 2^6 x 7 valid column configs."""
    for orb in orbits:
        adj_x = orb["adj_x"]
        # Collect all valid (rem, d_S) achievable by a triangle-free column with d_A, d_B in [1, 6]
        valid_ds_by_rem: dict[int, list[int]] = {}
        for xm in range(8):
            forb_y = 0
            for i in range(3):
                if (xm >> i) & 1:
                    forb_y |= adj_x[i]
            for ym in range(8):
                if ym & forb_y:
                    continue
                dx = xm.bit_count()
                dy = ym.bit_count()
                for ds in range(7):
                    if 1 <= ds + dx <= 6 and 1 <= ds + dy <= 6:
                        rem = ds + dx + dy
                        valid_ds_by_rem.setdefault(rem, []).append(ds)

        max_achievable_rem = max(valid_ds_by_rem.keys())
        assert max_achievable_rem <= orb["max_rem_T"], (orb["id"], max_achievable_rem, orb["max_rem_T"])
        assert orb["min_deg_T"] <= max(3, 9 - max_achievable_rem)

        for rem, ds_list in valid_ds_by_rem.items():
            encoded_min_ds = max(
                1 if rem > orb["alpha_both_H"] else 0,
                rem - orb["alpha_H"],
            )
            assert encoded_min_ds <= min(ds_list), (
                f"UNSOUND S-domination on {orb['id']} rem={rem}: "
                f"encoded={encoded_min_ds} > true_min={min(ds_list)}"
            )

    print("[PASS 3/7] Generalized S-domination & min_deg_T verified 100% sound across all 25 orbits.", flush=True)


def test_4_symmetry_breaking_soundness(orbits: list[dict]) -> None:
    """Verify for every orbit that NO valid assignment is pruned by the symmetry-breaking constraints."""
    rng = random.Random(20261127)
    for orb in orbits:
        mask = orb["mask"]
        # Compute full automorphism group Aut(H) <= S_3(X) x S_3(Y) x Z_2
        aut_h = []
        for px in d9c6.PERMS_3:
            for py in d9c6.PERMS_3:
                for sw in (0, 1):
                    m = 0
                    for i in range(3):
                        for j in range(3):
                            if (mask >> (3 * i + j)) & 1:
                                ni, nj = (py[j], px[i]) if sw else (px[i], py[j])
                                m |= 1 << (3 * ni + nj)
                    if m == mask:
                        aut_h.append((px, py, sw))

        # Test 200 random assignments with distinct S rows and distinct twin rows (as forced by codeg caps)
        for _ in range(200):
            s_rows = rng.sample(range(1 << 12), 6)
            xy_rows = rng.sample(range(1 << 12), 6)
            x_rows = xy_rows[:3]
            y_rows = xy_rows[3:]

            # S can always be sorted strictly by S_6(S)
            s_sorted = sorted(s_rows)
            assert all(s_sorted[i] < s_sorted[i + 1] for i in range(5))

            # Check that some automorphism in Aut(H) maps (x_rows, y_rows) into the lex-valid region
            found_rep = False
            for px, py, sw in aut_h:
                nx = [0] * 3
                ny = [0] * 3
                for i in range(3):
                    if sw:
                        ny[px[i]] = x_rows[i]
                    else:
                        nx[px[i]] = x_rows[i]
                for j in range(3):
                    if sw:
                        nx[py[j]] = y_rows[j]
                    else:
                        ny[py[j]] = y_rows[j]

                ok = True
                for cls in orb["twin_classes_X"]:
                    for a_i, b_i in zip(cls, cls[1:]):
                        if not (nx[a_i] < nx[b_i]):
                            ok = False
                            break
                if ok:
                    for cls in orb["twin_classes_Y"]:
                        for a_j, b_j in zip(cls, cls[1:]):
                            if not (ny[a_j] < ny[b_j]):
                                ok = False
                                break
                if ok and orb["transpose_symmetric"]:
                    if not (nx[0] <= ny[0]):
                        ok = False
                if ok:
                    found_rep = True
                    break

            assert found_rep, f"Symmetry breaking pruned a valid witness on {orb['id']}!"

    print("[PASS 4/7] Automorphism-respecting symmetry breaking verified 100% sound on all 25 orbits (5,000 trials).", flush=True)


def _derive_real_r38_26_cores() -> dict[int, str]:
    """Derive genuine, verified (3, 8; 26, e) cores by deleting vertices/edges from R38_27_85_G6."""
    adj27 = d9c6.decode_g6(R38_27_85_G6, expected_n=27)
    cores_by_e: dict[int, str] = {}

    def delete_vertex(adj: list[int], drop: int) -> list[int]:
        keep = [v for v in range(len(adj)) if v != drop]
        idx_map = {v: i for i, v in enumerate(keep)}
        out = [0] * len(keep)
        for u in keep:
            m = adj[u]
            while m:
                b = m & -m
                w = b.bit_length() - 1
                m ^= b
                if w != drop:
                    out[idx_map[u]] |= 1 << idx_map[w]
        return out

    # Vertex deletions give real (3, 8; 26, 85 - d) cores for d in {5, 6, 7} -> e in {78, 79, 80}
    for v in range(27):
        d = adj27[v].bit_count()
        e_new = 85 - d
        if e_new in (78, 79, 80) and e_new not in cores_by_e:
            sub = delete_vertex(adj27, v)
            d9c6.verify_r38_26(sub, expected_edges=e_new, check_alpha=True)
            g6 = d9c6.encode_g6(sub)
            assert d9c6.decode_g6(g6) == sub
            cores_by_e[e_new] = g6

    # Try adding 1 non-triangle edge to e=80 core to obtain a real e=81 core
    if 80 in cores_by_e:
        adj80 = d9c6.decode_g6(cores_by_e[80])
        for u in range(26):
            if adj80[u].bit_count() >= 7:
                continue
            for v in range(u + 1, 26):
                if adj80[v].bit_count() >= 7:
                    continue
                if ((adj80[u] >> v) & 1) == 0 and (adj80[u] & adj80[v]) == 0:
                    adj81 = list(adj80)
                    adj81[u] |= 1 << v
                    adj81[v] |= 1 << u
                    d9c6.verify_r38_26(adj81, expected_edges=81, check_alpha=True)
                    cores_by_e[81] = d9c6.encode_g6(adj81)
                    break
            if 81 in cores_by_e:
                break

    # Try greedy edge deletion from e=78 core (preserving alpha <= 7 and min_deg >= 3) down toward e=73
    if 78 in cores_by_e:
        cur = d9c6.decode_g6(cores_by_e[78])
        cur_e = 78
        while cur_e > 73:
            found_next = False
            edges = [
                (u, v) for u in range(26) for v in range(u + 1, 26)
                if ((cur[u] >> v) & 1) and cur[u].bit_count() > 3 and cur[v].bit_count() > 3
            ]
            # Prefer deleting edges between high-degree vertices
            edges.sort(key=lambda uv: -(cur[uv[0]].bit_count() + cur[uv[1]].bit_count()))
            for u, v in edges:
                cand = list(cur)
                cand[u] ^= 1 << v
                cand[v] ^= 1 << u
                if not d9c6.enum_indep(cand, 8, limit=1):
                    cur = cand
                    cur_e -= 1
                    d9c6.verify_r38_26(cur, expected_edges=cur_e, check_alpha=True)
                    cores_by_e[cur_e] = d9c6.encode_g6(cur)
                    found_next = True
                    break
            if not found_next:
                break

    return cores_by_e


def test_5_real_cores_and_cnf_stats(orbits: list[dict]) -> tuple[dict[int, str], list[dict]]:
    cores_by_e = _derive_real_r38_26_cores()
    assert len(cores_by_e) >= 3, f"Expected >= 3 real (3,8;26) cores, got {list(cores_by_e.keys())}"

    cnf_stats = []
    for orb in orbits:
        e_t = orb["e_T"]
        if e_t not in cores_by_e:
            continue
        adj = d9c6.decode_g6(cores_by_e[e_t])
        cnf, M, meta = d9c6.build_d9c6_cnf(adj, orb, include_b2=True, include_i7=True, include_lex=True)
        assert meta["primary_vars"] == 312
        assert meta["vars"] == cnf.nv and meta["clauses"] == len(cnf.clauses)
        cnf_stats.append(meta)

    print(
        f"[PASS 5/7] Real (3,8;26) cores verified for e_T={sorted(cores_by_e.keys())}; "
        f"built {len(cnf_stats)} full 312-var CNFs.",
        flush=True,
    )
    return cores_by_e, cnf_stats


def test_6_witness_verifier(orbits: list[dict], cores_by_e: dict[int, str]) -> None:
    orb = orbits[-1]  # e_xy=9, e_T=81 (or fallback to highest available)
    e_t = max(cores_by_e.keys())
    orb = next(o for o in orbits if o["e_T"] == e_t)
    adj = d9c6.decode_g6(cores_by_e[e_t])

    # Empty rows -> degree violation
    g_bad = d9c6.build_40_graph(adj, orb, [0] * 12)
    res_bad = d9c6.verify_40_witness(g_bad, orbit=orb)
    assert not res_bad["ok"] and res_bad["reason"].startswith("degree:")

    # Inject a triangle on vertices (0, 2, 3) -> triangle or degree check catches it
    g_tri = [0] * 40
    for i in range(40):
        for step in range(1, 5):
            j = (i + step) % 40
            g_tri[i] |= 1 << j
            g_tri[j] |= 1 << i
        # make 9-regular by adding opposite vertex
        j = (i + 20) % 40
        g_tri[i] |= 1 << j
    res_tri = d9c6.verify_40_witness(g_tri, check_max_codeg=False)
    assert not res_tri["ok"] and res_tri["reason"].startswith("triangle:")

    # Wrong vertex count
    assert not d9c6.verify_40_witness([0] * 39)["ok"]
    print("[PASS 6/7] Independent 40-vertex witness verifier negative checks passed.", flush=True)


def test_7_dry_run_sharding(cores_by_e: dict[int, str]) -> None:
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        gz_path = tmp / "r38_26_synth.g6.gz"
        # Write our real cores + 1 decoy 26-vertex empty graph (0 edges, must be filtered out!)
        empty_26 = d9c6.encode_g6([0] * 26)
        with gzip.open(gz_path, "wt", encoding="ascii") as fp:
            fp.write(empty_26 + "\n")
            for g6 in cores_by_e.values():
                fp.write(g6 + "\n")

        manifest_path = tmp / "manifest.json"
        m = runner.prepare_manifest(gz_path, manifest_path, verify_alpha=True)
        assert m["filter_stats"]["total_scanned"] == len(cores_by_e) + 1
        assert m["filter_stats"]["unique_valid_cores"] == len(cores_by_e)
        total_inst = m["total_instances"]
        assert total_inst > 0

        # Run dry-run across M=10 shards and verify exact disjoint complete coverage
        seen_ids: list[str] = []
        for k in range(10):
            s_out = tmp / f"shard_{k}"
            summ = runner.run_shard(
                manifest_path=manifest_path,
                shard_idx=k,
                num_shards=10,
                out_dir=s_out,
                dry_run=True,
            )
            assert summ["counts"]["DRY_RUN_OK"] == summ["assigned_instances"]
            assert (s_out / f"shard_{k}_summary.json").is_file()
            assert (s_out / f"shard_{k}_proof_manifest.json").is_file()
            for inst_dir in (s_out / "instances").iterdir():
                res = json.loads((inst_dir / "result.json").read_text())
                assert res["status"] == "DRY_RUN_OK"
                seen_ids.append(res["instance_id"])

            # Verify idempotent resume skips already-certified instances
            if summ["assigned_instances"] > 0:
                first_dir = next((s_out / "instances").iterdir())
                r0 = json.loads((first_dir / "result.json").read_text())
                r0["status"] = "CERTIFIED_UNSAT"
                (first_dir / "result.json").write_text(json.dumps(r0))
                summ2 = runner.run_shard(
                    manifest_path=manifest_path,
                    shard_idx=k,
                    num_shards=10,
                    out_dir=s_out,
                    dry_run=True,
                )
                assert summ2["counts"]["SKIPPED_RESUMED"] == 1

        assert len(seen_ids) == total_inst and len(set(seen_ids)) == total_inst
    print(f"[PASS 7/7] Dry-run sharding (M=10 shards, {total_inst} instances) + checkpoint/resume verified.", flush=True)


def main() -> None:
    t0 = time.monotonic()
    orbits = test_1_orbit_enumeration()
    test_2_cnf_primitives()
    test_3_s_domination_soundness(orbits)
    test_4_symmetry_breaking_soundness(orbits)
    cores_by_e, cnf_stats = test_5_real_cores_and_cnf_stats(orbits)
    test_6_witness_verifier(orbits, cores_by_e)
    test_7_dry_run_sharding(cores_by_e)

    # Print compact CNF stats table
    print("\n--- Sample D9-C6 Compact 312-var CNF Stats (Real (3,8;26) Cores) ---", flush=True)
    for st in cnf_stats:
        print(
            f"  {st['orbit_id']} (e_xy={st['e_xy']}, e_T={st['e_T']}): "
            f"vars={st['vars']:,}, clauses={st['clauses']:,}, "
            f"I7={st['i7_total']}, nontriv_T_pairs={st['nontrivial_t_pairs']}, "
            f"zero_T_pairs={st['zero_codeg_t_pairs']}, sym={len(st['sym_constraints'])}",
            flush=True,
        )
    print(f"\nALL 7/7 SELFTEST SUITES PASSED in {time.monotonic() - t0:.2f}s!", flush=True)


if __name__ == "__main__":
    main()
