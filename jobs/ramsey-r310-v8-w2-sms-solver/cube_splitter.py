#!/usr/bin/env python3
"""
First-Principles Cube-and-Conquer / High-Impact-Edge Splitter
for Ramsey R(3,10) V8 Hard Surviving Leaves (Wave 2 Subagent 5).

Capabilities:
  1. High-Impact Edge Variable Selection:
     - Restricts branching to free edge variables (1..780 by default).
     - Combines Jeroslow-Wang clause weights, Ramsey structural block priority
       (X x Y > X x T & Y x T > T x T), and exact Boolean Constraint Propagation
       (BCP) lookahead product score `(prop_pos + 1) * (prop_neg + 1)`.
  2. Uniform 2^k Splitting AND Adaptive Tree Splitting (any target cube count <= 10+):
     - Produces disjoint, exhaustive cubes C_0, ..., C_{m-1}.
  3. Triple-Checked Formal Exhaustiveness & Disjointness Proof:
     - Pairwise disjointness check: every pair (C_i, C_j) has an opposing literal.
     - Exact rational measure check: sum_i 2^{-|C_i|} == 1 (using fractions.Fraction).
     - Exact truth-table check (for <= 16 distinct branching vars) AND exact DPLL
       refutation of `AND_i (NOT C_i)`, plus emits `tautology_negation.cnf` so an
       external solver + drat-trim/lrat-check can independently certify completeness!
  4. Per-Cube DIMACS Materialization + Optional Single-Cube Kissat/LRAT Execution.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import sys
import time
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import sms_partition_driver as spd


# ---------------------------------------------------------------------------
# Fast Pure-Python Boolean Constraint Propagation (BCP) for Lookahead Scoring
# ---------------------------------------------------------------------------

def extract_unit_assignments(clauses: Sequence[Sequence[int]]) -> Tuple[Dict[int, bool], bool]:
    """Propagate initial unit clauses; returns (assignment_map, has_conflict)."""
    assign: Dict[int, bool] = {}
    queue: List[int] = [cl[0] for cl in clauses if len(cl) == 1]
    if any(len(cl) == 0 for cl in clauses):
        return assign, True
    while queue:
        lit = queue.pop()
        v = abs(lit)
        val = lit > 0
        if v in assign:
            if assign[v] != val:
                return assign, True
            continue
        assign[v] = val
    return assign, False


def build_watch_index(
    clauses: Sequence[Sequence[int]],
    base_assign: Dict[int, bool],
    max_clause_len: int = 8,
) -> Tuple[List[List[int]], Dict[int, List[int]]]:
    """Simplify clauses under `base_assign` and index short clauses for fast BCP lookahead."""
    short_clauses: List[List[int]] = []
    occ: Dict[int, List[int]] = defaultdict(list)
    for cl in clauses:
        if len(cl) > max_clause_len:
            continue
        rem: List[int] = []
        sat = False
        for lit in cl:
            v = abs(lit)
            if v in base_assign:
                if base_assign[v] == (lit > 0):
                    sat = True
                    break
            else:
                rem.append(lit)
        if sat:
            continue
        cid = len(short_clauses)
        short_clauses.append(rem)
        for lit in rem:
            occ[-lit].append(cid)  # indexed by falsifying literal
    return short_clauses, occ


def bcp_propagate(
    short_clauses: Sequence[Sequence[int]],
    occ: Dict[int, List[int]],
    assumptions: Sequence[int],
) -> Tuple[int, bool, Dict[int, bool]]:
    """Run exact BCP over `short_clauses` starting from `assumptions`.

    Returns (num_assigned, conflict, assignment_dict).
    """
    assign: Dict[int, bool] = {}
    queue: List[int] = list(assumptions)
    while queue:
        lit = queue.pop()
        v = abs(lit)
        val = lit > 0
        if v in assign:
            if assign[v] != val:
                return len(assign), True, assign
            continue
        assign[v] = val
        for cid in occ.get(lit, ()):
            cl = short_clauses[cid]
            unassigned_lit = 0
            unassigned_cnt = 0
            sat = False
            for cl_lit in cl:
                cv = abs(cl_lit)
                if cv in assign:
                    if assign[cv] == (cl_lit > 0):
                        sat = True
                        break
                else:
                    unassigned_lit = cl_lit
                    unassigned_cnt += 1
                    if unassigned_cnt > 1:
                        break
            if sat:
                continue
            if unassigned_cnt == 0:
                return len(assign), True, assign
            if unassigned_cnt == 1:
                queue.append(unassigned_lit)
    return len(assign), False, assign


# ---------------------------------------------------------------------------
# High-Impact Variable Scoring (JW + Ramsey Block Priority + BCP Lookahead)
# ---------------------------------------------------------------------------

def ramsey_edge_block_weight(var: int, d: Optional[int], q: Optional[int], n: int = 40) -> float:
    """Structural priority weight for Ramsey R(3,10) edge variables."""
    if d is None or q is None or var > spd.num_edge_vars(n):
        return 1.0
    u, v = spd.var_to_edge(var, n)
    # 0 = root0, 1 = root1, X = [2..d], Y = [d+1..d+q-1], T = [d+q..n-1]
    def blk(w: int) -> str:
        if w <= 1:
            return "R"
        if w <= d:
            return "X"
        if w < d + q:
            return "Y"
        return "T"

    bu, bv = blk(u), blk(v)
    pair = tuple(sorted((bu, bv)))
    if pair == ("X", "Y"):
        return 3.0  # Highest impact: determines König bipartite skeleton G[X u Y]
    if pair in (("T", "X"), ("T", "Y")):
        return 1.8  # Cross-edges driving triangle-free pruning & degX/degY caps
    if pair == ("T", "T"):
        return 1.0
    return 0.5


def select_best_branch_var(
    clauses: Sequence[Sequence[int]],
    base_assign: Dict[int, bool],
    assumptions: Sequence[int],
    max_branch_var: int = 780,
    d: Optional[int] = None,
    q: Optional[int] = None,
    n: int = 40,
    top_k_lookahead: int = 24,
) -> Tuple[int, dict]:
    """Select the single highest-impact free variable for splitting a leaf."""
    short_clauses, occ = build_watch_index(clauses, base_assign, max_clause_len=8)
    _, init_conflict, cur_assign = bcp_propagate(short_clauses, occ, assumptions)
    if init_conflict:
        raise ValueError("Leaf assumptions already conflict under BCP")

    fixed_vars = set(base_assign.keys()) | set(cur_assign.keys())

    # Jeroslow-Wang scores on active clauses
    jw_pos: Dict[int, float] = defaultdict(float)
    jw_neg: Dict[int, float] = defaultdict(float)
    candidates: Set[int] = set()

    for cl in clauses:
        if len(cl) > 12:
            continue
        w = 2.0 ** (-len(cl))
        for lit in cl:
            v = abs(lit)
            if v <= max_branch_var and v not in fixed_vars:
                candidates.add(v)
                if lit > 0:
                    jw_pos[v] += w
                else:
                    jw_neg[v] += w

    if not candidates:
        # Fallback: any free variable up to max_branch_var
        for v in range(1, max_branch_var + 1):
            if v not in fixed_vars:
                candidates.add(v)
                break
    if not candidates:
        raise RuntimeError("No free variables available to branch on")

    # Pre-rank by balanced JW * structural block weight
    def pre_score(v: int) -> float:
        bw = ramsey_edge_block_weight(v, d, q, n)
        return ((jw_pos[v] + 0.1) * (jw_neg[v] + 0.1)) * bw

    ranked = sorted(candidates, key=lambda v: (-pre_score(v), v))[:top_k_lookahead]

    best_v = ranked[0]
    best_score = -1.0
    best_info: dict = {}

    for v in ranked:
        bw = ramsey_edge_block_weight(v, d, q, n)
        n_pos, conf_pos, _ = bcp_propagate(short_clauses, occ, list(assumptions) + [v])
        n_neg, conf_neg, _ = bcp_propagate(short_clauses, occ, list(assumptions) + [-v])
        delta_pos = max(0, n_pos - len(cur_assign))
        delta_neg = max(0, n_neg - len(cur_assign))
        # Strongly reward variables where BOTH branches trigger propagation
        # (and reward immediate unit-conflict detection on one side)
        eff_pos = (delta_pos + 10) if conf_pos else (delta_pos + 1)
        eff_neg = (delta_neg + 10) if conf_neg else (delta_neg + 1)
        score = float(eff_pos * eff_neg) * bw + 1e-3 * pre_score(v)
        if score > best_score:
            best_score = score
            best_v = v
            best_info = {
                "var": v,
                "score": round(score, 4),
                "prop_pos": delta_pos,
                "prop_neg": delta_neg,
                "conflict_pos": conf_pos,
                "conflict_neg": conf_neg,
                "block_weight": bw,
                "jw_pos": round(jw_pos[v], 4),
                "jw_neg": round(jw_neg[v], 4),
            }
    return best_v, best_info


# ---------------------------------------------------------------------------
# Uniform 2^k and Adaptive Tree Cube Generators
# ---------------------------------------------------------------------------

def generate_uniform_cubes(
    clauses: Sequence[Sequence[int]],
    depth: int,
    max_branch_var: int = 780,
    d: Optional[int] = None,
    q: Optional[int] = None,
    n: int = 40,
) -> Tuple[List[List[int]], List[dict]]:
    """Generate 2^depth disjoint, exhaustive cubes by branching on `depth` high-impact vars."""
    if depth < 1 or depth > 12:
        raise ValueError(f"depth must be in 1..12, got {depth}")
    base_assign, conflict = extract_unit_assignments(clauses)
    if conflict:
        raise ValueError("Input CNF is already UNSAT by unit propagation")

    chosen_vars: List[int] = []
    chosen_meta: List[dict] = []
    # Greedily select `depth` distinct variables
    temp_fixed = dict(base_assign)
    for _ in range(depth):
        v, info = select_best_branch_var(
            clauses, temp_fixed, assumptions=[], max_branch_var=max_branch_var, d=d, q=q, n=n
        )
        chosen_vars.append(v)
        chosen_meta.append(info)
        # Mark v as already chosen so next pick is distinct
        temp_fixed[v] = True

    cubes: List[List[int]] = []
    for signs in itertools.product((1, -1), repeat=depth):
        cubes.append([s * v for s, v in zip(signs, chosen_vars)])
    return cubes, chosen_meta


def generate_adaptive_cubes(
    clauses: Sequence[Sequence[int]],
    target_cubes: int,
    max_branch_var: int = 780,
    d: Optional[int] = None,
    q: Optional[int] = None,
    n: int = 40,
) -> Tuple[List[List[int]], List[dict]]:
    """Adaptively split the least-constrained leaf until `target_cubes` disjoint exhaustive cubes exist."""
    if target_cubes < 2 or target_cubes > 1024:
        raise ValueError(f"target_cubes must be in 2..1024, got {target_cubes}")
    base_assign, conflict = extract_unit_assignments(clauses)
    if conflict:
        raise ValueError("Input CNF is already UNSAT by unit propagation")

    leaves: List[List[int]] = [[]]
    split_history: List[dict] = []

    while len(leaves) < target_cubes:
        # Pick the shallowest leaf (tie-break by earliest index) to keep depth balanced
        leaf_idx = min(range(len(leaves)), key=lambda i: (len(leaves[i]), i))
        leaf = leaves.pop(leaf_idx)
        v, info = select_best_branch_var(
            clauses, base_assign, assumptions=leaf, max_branch_var=max_branch_var, d=d, q=q, n=n
        )
        split_history.append({"parent_cube": list(leaf), "split_var": v, "info": info})
        leaves.append(leaf + [v])
        leaves.append(leaf + [-v])

    return leaves, split_history


# ---------------------------------------------------------------------------
# Formal Exhaustiveness & Disjointness Tautology Verification
# ---------------------------------------------------------------------------

def _dpll_is_sat(clauses: List[List[int]]) -> bool:
    """Exact pure-Python DPLL SAT solver for verifying `AND_i (NOT C_i)` is UNSAT."""
    # Simplify via unit propagation
    clauses = [list(c) for c in clauses]
    while True:
        if any(len(c) == 0 for c in clauses):
            return False
        if not clauses:
            return True
        unit = next((c[0] for c in clauses if len(c) == 1), None)
        if unit is None:
            break
        new_clauses: List[List[int]] = []
        for c in clauses:
            if unit in c:
                continue
            if -unit in c:
                new_clauses.append([x for x in c if x != -unit])
            else:
                new_clauses.append(c)
        clauses = new_clauses

    # Choose literal from shortest clause
    shortest = min(clauses, key=len)
    lit = shortest[0]
    for branch in (lit, -lit):
        reduced: List[List[int]] = []
        for c in clauses:
            if branch in c:
                continue
            if -branch in c:
                reduced.append([x for x in c if x != -branch])
            else:
                reduced.append(c)
        if _dpll_is_sat(reduced):
            return True
    return False


def verify_cube_partition(
    cubes: Sequence[Sequence[int]],
    truth_table_max_vars: int = 16,
) -> dict:
    """Formally prove that `cubes` is a disjoint, exhaustive partition of truth assignments.

    Checks:
      1. Validity: no empty list of cubes, no duplicate/contradictory literals within any cube.
      2. Pairwise disjointness: for all i < j, exists literal l in C_i with -l in C_j.
      3. Exact rational probability measure: sum_i 2^{-|C_i|} == 1.
      4. Exact DPLL proof that `AND_i (NOT C_i)` is UNSAT (hence `OR_i C_i === TOP`).
      5. Exact truth-table enumeration (when #distinct vars <= `truth_table_max_vars`):
         every assignment satisfies EXACTLY 1 cube.
    """
    if not cubes:
        return {"valid": False, "error": "Empty cube list"}

    norm_cubes: List[Set[int]] = []
    all_vars: Set[int] = set()
    for idx, c in enumerate(cubes):
        s: Set[int] = set()
        for lit in c:
            if lit == 0:
                return {"valid": False, "error": f"Cube {idx} contains literal 0"}
            if -lit in s:
                return {"valid": False, "error": f"Cube {idx} is self-contradictory on var {abs(lit)}"}
            s.add(lit)
            all_vars.add(abs(lit))
        norm_cubes.append(s)

    # 1. Pairwise disjointness
    m = len(norm_cubes)
    for i in range(m):
        ci = norm_cubes[i]
        for j in range(i + 1, m):
            cj = norm_cubes[j]
            if not any(-lit in cj for lit in ci):
                return {
                    "valid": False,
                    "error": f"Cubes {i} and {j} are NOT disjoint: {sorted(ci)} vs {sorted(cj)}",
                }

    # 2. Exact rational measure check
    measure = sum((Fraction(1, 1 << len(c)) for c in norm_cubes), Fraction(0, 1))
    measure_ok = measure == Fraction(1, 1)

    # 3. Exact DPLL check of negation `AND_i (NOT C_i)`
    neg_clauses = [[-lit for lit in sorted(c, key=lambda x: (abs(x), x))] for c in norm_cubes]
    dpll_unsat = not _dpll_is_sat(neg_clauses)

    # 4. Exact truth-table check if variable count is small
    sorted_vars = sorted(all_vars)
    tt_checked = False
    tt_ok: Optional[bool] = None
    if len(sorted_vars) <= truth_table_max_vars:
        tt_checked = True
        tt_ok = True
        for bits in itertools.product((False, True), repeat=len(sorted_vars)):
            env = dict(zip(sorted_vars, bits))
            hits = 0
            for c in norm_cubes:
                if all(env[abs(lit)] == (lit > 0) for lit in c):
                    hits += 1
            if hits != 1:
                tt_ok = False
                break

    valid = measure_ok and dpll_unsat and (tt_ok is not False)
    return {
        "valid": valid,
        "num_cubes": m,
        "num_branch_vars": len(sorted_vars),
        "branch_vars": sorted_vars,
        "pairwise_disjoint": True,
        "exact_measure": str(measure),
        "measure_equals_one": measure_ok,
        "dpll_negation_unsat": dpll_unsat,
        "truth_table_checked": tt_checked,
        "truth_table_exact_one_hit": tt_ok,
    }


# ---------------------------------------------------------------------------
# Materialization & Manifest Generation
# ---------------------------------------------------------------------------

def materialize_cubes(
    base_cnf_path: Path,
    cubes: Sequence[Sequence[int]],
    out_dir: Path,
    split_meta: Sequence[dict],
    extra_meta: Optional[dict] = None,
) -> dict:
    """Verify cubes, write per-cube CNFs, `cubes.icnf`, `tautology_negation.cnf`, and `manifest.json`."""
    proof = verify_cube_partition(cubes)
    if not proof["valid"]:
        raise ValueError(f"Refusing to materialize invalid cube partition: {proof}")

    out_dir.mkdir(parents=True, exist_ok=True)
    nv, base_clauses = spd.read_dimacs(base_cnf_path)

    # Write formal tautology negation CNF (`AND_i NOT C_i` -> must be UNSAT)
    neg_clauses = [[-lit for lit in c] for c in cubes]
    max_branch_v = max((abs(lit) for c in cubes for lit in c), default=1)
    taut_cnf_path = out_dir / "tautology_negation.cnf"
    spd.write_dimacs(
        taut_cnf_path,
        max_branch_v,
        neg_clauses,
        comments=[
            "Negation of disjunction of cubes: UNSAT proves OR_i C_i === TOP (100% exhaustive)."
        ],
    )

    # Write standard iCNF cubes file
    icnf_path = out_dir / "cubes.icnf"
    with open(icnf_path, "w", encoding="utf-8") as f:
        f.write("p inccnf\n")
        for c in cubes:
            f.write("a " + " ".join(str(x) for x in c) + " 0\n")

    cube_entries: List[dict] = []
    for idx, c in enumerate(cubes):
        cube_cnf = out_dir / f"cube_{idx:03d}.cnf"
        unit_clauses = [[lit] for lit in c]
        spd.write_dimacs(
            cube_cnf,
            nv,
            list(base_clauses) + unit_clauses,
            comments=[
                f"base_cnf={base_cnf_path.name} cube_idx={idx}/{len(cubes)}",
                f"assumptions={' '.join(str(x) for x in c)}",
            ],
        )
        cube_entries.append(
            {
                "idx": idx,
                "assumptions": list(c),
                "cnf_file": cube_cnf.name,
                "cnf_sha256": spd.sha256_file(cube_cnf),
                "num_vars": nv,
                "num_clauses": len(base_clauses) + len(unit_clauses),
            }
        )

    manifest = {
        "base_cnf": str(base_cnf_path),
        "base_cnf_sha256": spd.sha256_file(base_cnf_path),
        "base_vars": nv,
        "base_clauses": len(base_clauses),
        "tautology_proof": proof,
        "tautology_negation_cnf": taut_cnf_path.name,
        "icnf_file": icnf_path.name,
        "split_meta": list(split_meta),
        "extra_meta": extra_meta or {},
        "cubes": cube_entries,
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return manifest


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="Cube-and-Conquer high-impact edge splitter with formal tautology proof."
    )
    sub = ap.add_subparsers(dest="cmd", required=True)

    sp = sub.add_parser("split", help="Split a DIMACS CNF into disjoint, exhaustive cubes.")
    sp.add_argument("--dimacs", type=Path, required=True, help="Input DIMACS CNF.")
    sp.add_argument("--out", type=Path, required=True, help="Output directory for cube CNFs & manifest.")
    sp.add_argument("--mode", choices=["uniform", "adaptive"], default="uniform")
    sp.add_argument("--depth", type=int, default=2, help="Split depth k (uniform mode -> 2^k cubes).")
    sp.add_argument("--target-cubes", type=int, default=4, help="Target cube count (adaptive mode).")
    sp.add_argument("--max-branch-var", type=int, default=780, help="Restrict branching to vars <= this id.")
    sp.add_argument("--d", type=int, default=None, help="Optional Ramsey parameter d for X/Y/T priority.")
    sp.add_argument("--q", type=int, default=None, help="Optional Ramsey parameter q for X/Y/T priority.")
    sp.add_argument("--vertices", type=int, default=40)

    sv = sub.add_parser("solve-cube", help="Solve one materialized cube with Kissat + DRAT/LRAT.")
    sv.add_argument("--manifest", type=Path, required=True, help="Path to manifest.json.")
    sv.add_argument("--cube-idx", type=int, required=True, help="0-based cube index.")
    sv.add_argument("--out", type=Path, required=True, help="Output directory for this cube's proof.")
    sv.add_argument("--seconds", type=int, default=1200)
    sv.add_argument("--dry-run", action="store_true")

    args = ap.parse_args(argv)

    if args.cmd == "split":
        t0 = time.monotonic()
        _, clauses = spd.read_dimacs(args.dimacs)
        if args.mode == "uniform":
            cubes, meta = generate_uniform_cubes(
                clauses,
                depth=args.depth,
                max_branch_var=args.max_branch_var,
                d=args.d,
                q=args.q,
                n=args.vertices,
            )
        else:
            cubes, meta = generate_adaptive_cubes(
                clauses,
                target_cubes=args.target_cubes,
                max_branch_var=args.max_branch_var,
                d=args.d,
                q=args.q,
                n=args.vertices,
            )
        manifest = materialize_cubes(
            args.dimacs,
            cubes,
            args.out,
            split_meta=meta,
            extra_meta={
                "split_mode": args.mode,
                "split_wall_s": round(time.monotonic() - t0, 3),
                "d": args.d,
                "q": args.q,
            },
        )
        print(json.dumps(manifest["tautology_proof"], indent=2), flush=True)
        return 0

    if args.cmd == "solve-cube":
        manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
        cubes = manifest["cubes"]
        if not (0 <= args.cube_idx < len(cubes)):
            raise IndexError(f"cube_idx={args.cube_idx} out of range 0..{len(cubes) - 1}")
        entry = cubes[args.cube_idx]
        cnf_path = args.manifest.parent / entry["cnf_file"]
        res = spd.run_kissat_and_lrat(cnf_path, args.out, seconds=args.seconds, dry_run=args.dry_run)
        out_payload = {
            "cube_idx": args.cube_idx,
            "assumptions": entry["assumptions"],
            "cnf_file": entry["cnf_file"],
            "cnf_sha256": entry["cnf_sha256"],
            "result": res,
        }
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out / f"cube_{args.cube_idx:03d}_result.json").write_text(
            json.dumps(out_payload, indent=2) + "\n", encoding="utf-8"
        )
        print(json.dumps(out_payload, indent=2), flush=True)
        return 0

    return 1


if __name__ == "__main__":
    raise SystemExit(main())
