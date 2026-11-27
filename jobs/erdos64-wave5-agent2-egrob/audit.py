#!/usr/bin/env python3
import json
import re
import subprocess
import sys
from pathlib import Path

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

THEOREMS = [
    "E64Wave5Agent2EGRob.minimal_bad2_exists",
    "E64Wave5Agent2EGRob.minimal_bad2_exact_two_defects",
    "E64Wave5Agent2EGRob.minimal_bad2_defects_nonadjacent",
    "E64Wave5Agent2EGRob.minimal_bad2_defect_neighbors_cubic",
    "E64Wave5Agent2EGRob.minimal_bad2_high_independent",
    "E64Wave5Agent2EGRob.minimal_bad2_nonbipartite",
    "E64Wave5Agent2EGRob.minimal_bad2_two_edge_connected",
    "E64Wave5Agent2EGRob.minimal_bad2_no_cut_vertex",
    "E64Wave5Agent2EGRob.minimal_bad2_no_defect_free_two_cut",
    "E64Wave5Agent2EGRob.minimal_bad2_no_defect_free_two_vertex_cut",
    "E64Wave5Agent2EGRob.eg2_core_completion_three_edge_connected",
    "E64Wave5Agent2EGRob.eg2_core_completion_three_connected",
    "E64Wave5Agent2EGRob.eg_rob_3conn_core_implies_eg2",
    "E64Wave5Agent2EGRob.eg2_implies_eg_rob",
    "E64Wave5Agent2EGRob.eg2_iff_eg_rob_3conn_core",
    "E64Wave5Agent2EGRob.eg2_iff_eg_rob_3conn",
    "E64Wave5Agent2EGRob.eg2_iff_eg_rob_3ec",
    "E64Wave5Agent2EGRob.eg_rob_3conn_core_implies_erdos64",
    "E64Wave5Agent2EGRob.minimal_bad2_cubic_at_most_two_high_neighbors",
    "E64Wave5Agent2EGRob.minimal_bad2_defect_neighbor_at_most_one_high_neighbor",
    "E64Wave5Agent2EGRob.minimal_bad2_cubic_density_bound",
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
        "module": "Wave5Agent2EGRob",
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
