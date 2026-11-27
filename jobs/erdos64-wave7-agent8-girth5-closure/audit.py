#!/usr/bin/env python3
import json
import re
import subprocess
import sys
from pathlib import Path

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

THEOREMS = [
    "E64Wave7Agent8.pentagram_p3_closes_c8",
    "E64Wave7Agent8.pentagram_cover_forces_p3",
    "E64Wave7Agent8.c5_star_covered_has_c8",
    "E64Wave7Agent8.c5_external_neighbors_distinct_of_girth5",
    "E64Wave7Agent8.c5_star_covered_girth5_has_pow2_cycle",
    "E64Wave7Agent8.two_paths_form_simple_cycle",
    "E64Wave7Agent8.same_scale_fermat_no_single_edge_overlap",
    "E64Wave7Agent8.same_scale_fermat_forbidden_overlaps",
    "E64Wave7Agent8.cross_scale_fermat_forbidden_overlap",
    "E64Wave7Agent8.disjoint_fermat_two_bridge_sum_obstruction",
    "E64Wave7Agent8.disjoint_fermat_two_bridge_diff3_obstruction",
    "E64Wave7Agent8.odd_cycle_adjuster_realizes_unit_interval",
    "E64Wave7Agent8.odd_cycle_adjuster_necklace_closes_pow2",
    "E64Wave7Agent8.even_cycle_adjuster_realizes_even_interval",
    "E64Wave7Agent8.even_cycle_adjuster_necklace_closes_pow2",
]

def main():
    log_path = Path(sys.argv[1])
    out_path = Path(sys.argv[2])
    text = log_path.read_text()

    axioms_map = {}
    pat = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.MULTILINE | re.DOTALL)
    for m in pat.finditer(text):
        name = m.group(1).strip()
        axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
        axioms_map[name] = sorted(axs)

    missing = [t for t in THEOREMS if t not in axioms_map]
    bad = {}
    for t in THEOREMS:
        if t in axioms_map:
            extra = [a for a in axioms_map[t] if a not in ALLOWED_AXIOMS]
            if extra:
                bad[t] = extra

    lean_ver = subprocess.check_output(["lean", "--version"], text=True).strip()
    report = {
        "status": "PASS" if (not missing and not bad) else "FAIL",
        "module": "Wave7Agent8Girth5Closure",
        "audited_count": len(THEOREMS),
        "lean_version": lean_ver,
        "missing_theorems": missing,
        "disallowed_axioms": bad,
        "axioms": {t: axioms_map.get(t, []) for t in THEOREMS},
    }
    out_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if missing or bad:
        sys.exit(1)

if __name__ == "__main__":
    main()
