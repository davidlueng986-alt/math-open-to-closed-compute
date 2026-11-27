#!/usr/bin/env python3
import json
import re
import subprocess
import sys
from pathlib import Path

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

THEOREMS = [
    "E64Wave8Agent6.c5_chord_forces_c4",
    "E64Wave8Agent6.c5_two_edges_sharing_vertex_forces_c3_or_c4",
    "E64Wave8Agent6.c5_split_dichotomy",
    "E64Wave8Agent6.two_cycle_double_bridge_four_cycles",
    "E64Wave8Agent6.disjoint_c5_double_edge_forces_pow2",
    "E64Wave8Agent6.c5_pow2_ring_arithmetic",
    "E64Wave8Agent6.c5_ring_realize_simple_cycle",
    "E64Wave8Agent6.c5_pow2_ring_forces_pow2_cycle",
    "E64Wave8Agent6.cubic_c5_quotient_pow2_cycle_lifts",
    "E64Wave8Agent6.minimal_counterexample_no_cubic_c5_quotient_delta3",
    "E64Wave8Agent6.c5_factor_minimal_counterexample_impossible",
    "E64Wave8Agent6.endpoint_chords_three_cycles",
    "E64Wave8Agent6.endpoint_chords_forbid_dyadic_gaps",
    "E64Wave8Agent6.posa_pivot_common_neighbor_c4",
    "E64Wave8Agent6.posa_pivot_inner_cycles",
    "E64Wave8Agent6.posa_pivot_between_cycles",
    "E64Wave8Agent6.posa_pivot_beyond_cycles",
    "E64Wave8Agent6.crossing_chords_six_cycle_spectrum",
    "E64Wave8Agent6.crossing_chords_pow2_forcing",
    "E64Wave8Agent6.cubic_shared_vertex_cycles_share_edge",
    "E64Wave8Agent6.girth9_closed_walk16_no_split",
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
        "module": "Wave8Agent6Posa2Factor",
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
