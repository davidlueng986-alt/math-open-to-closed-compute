import hashlib
import json
import re
import sys
from pathlib import Path

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

EXPECTED = [
    "E64Wave5Agent1EG2Core.minimal_bad2_connected",
    "E64Wave5Agent1EG2Core.minimal_bad2_two_edge_connected",
    "E64Wave5Agent1EG2Core.minimal_bad2_two_connected",
    "E64Wave5Agent1EG2Core.minimal_bad2_two_cut_normal_form",
    "E64Wave5Agent1EG2Core.minimal_bad2_v3_component_high_bottleneck",
    "E64Wave5Agent1EG2Core.minimal_bad2_no_v3_all_high_neighbors",
    "E64Wave5Agent1EG2Core.minimal_bad2_no_adjacent_two_high_disjoint",
    "E64Wave5Agent1EG2Core.minimal_bad2_defect_neighbor_at_most_one_high",
    "E64Wave5Agent1EG2Core.minimal_bad2_c4_free",
    "E64Wave5Agent1EG2Core.minimal_bad2_v3_density_two_thirds",
    "E64Wave5Agent1EG2Core.minimal_bad2_defect_dyadic_path",
    "E64Wave5Agent1EG2Core.minimal_bad2_defect_pair_contraction_edge_robust",
    "E64Wave5Agent1EG2Core.minimal_bad2_defect_pair_contraction_neighbor_robust",
    "E64Wave5Agent1EG2Core.minimal_bad2_delete_defect_nonbipartite",
    "E64Wave5Agent1EG2Core.minimal_bad2_odd_edge_transversal_constraints",
]


def main() -> None:
    out_dir = Path(sys.argv[1])
    text = (out_dir / "axioms.txt").read_text(encoding="utf-8")
    axioms = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S):
        name = m.group(1)
        raw = [a.strip() for a in m.group(2).split(",") if a.strip()]
        axioms[name] = sorted(set(raw))
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        axioms[m.group(1)] = []

    missing = [name for name in EXPECTED if name not in axioms]
    if missing:
        raise SystemExit(f"Missing expected theorems in axiom output: {missing}")

    bad = {k: sorted(set(v) - ALLOWED_AXIOMS) for k, v in axioms.items() if set(v) - ALLOWED_AXIOMS}
    if bad:
        raise SystemExit(f"Forbidden axioms detected: {bad}")

    lean_path = out_dir / "Wave5Agent1EG2Core.lean"
    sha = hashlib.sha256(lean_path.read_bytes()).hexdigest()

    result = {
        "status": "PASS",
        "module": "Wave5Agent1EG2Core",
        "audited_count": len(EXPECTED),
        "source_commit": (out_dir / "source_commit.txt").read_text(encoding="utf-8").strip(),
        "lean_version": (out_dir / "lean_version.txt").read_text(encoding="utf-8").strip(),
        "mathlib_commit": (out_dir / "mathlib_commit.txt").read_text(encoding="utf-8").strip(),
        "axioms": {k: axioms[k] for k in EXPECTED},
        "source_sha256": {"Wave5Agent1EG2Core.lean": sha},
        "scope": "Wave 5 Agent #1: 15 all-order structural reductions on EG2-CORE / MinimalBad2 (connectivity, 2-cut normal form, V3-V>=4 discharging & 2/3 cubic density, defect-pair contraction robustness, and G-u / G-e nonbipartiteness).",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
