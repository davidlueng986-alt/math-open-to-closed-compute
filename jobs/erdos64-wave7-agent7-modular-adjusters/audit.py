#!/usr/bin/env python3
import json
import os
import re
import subprocess
import sys

LEAN_FILE = sys.argv[1]
OUT_JSON = sys.argv[2]

THEOREMS = [
    "E64Wave7Agent7.signed_shift_subset_sum_realization",
    "E64Wave7Agent7.exists_pow2_mod_odd_in_window",
    "E64Wave7Agent7.pentagon_pure_shift3_closure",
    "E64Wave7Agent7.hexagon_pure_shift4_closure",
    "E64Wave7Agent7.heptagon_pure_shift5_closure",
    "E64Wave7Agent7.mixed_shift_1_and_3_breaks_mod3_obstruction",
    "E64Wave7Agent7.mixed_shift_ge2_ones_full_interval",
    "E64Wave7Agent7.two_factor_arc_partition",
    "E64Wave7Agent7.pentagon_arc_shifts",
    "E64Wave7Agent7.hexagon_arc_shifts",
    "E64Wave7Agent7.hasPow2Cycle_of_modular_adjuster_chain",
    "E64Wave7Agent7.cross_rewiring_neighbors_disjoint_and_nonadj",
    "E64Wave7Agent7.cross_rewiring_min_degree_three",
    "E64Wave7Agent7.cross_rewiring_length_lifting_arithmetic",
    "E64Wave7Agent7.no_repeated_cycle_pow2",
    "E64Wave7Agent7.cubic_no_edge_disjoint_cycles_sharing_vertex",
]

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

with open(LEAN_FILE, "r", encoding="utf-8") as f:
    src = f.read()

for forbidden in ["sorry", "admit", "native_decide", "axiom "]:
    if re.search(rf"\b{forbidden.strip()}\b", src):
        print(f"AUDIT FAIL: forbidden token {forbidden!r} found in {LEAN_FILE}", file=sys.stderr)
        sys.exit(1)

mathlib_dir = os.environ.get("MATHLIB_DIR", "/opt/mathlib4/DownstreamTest")
audit_code = src + "\n" + "\n".join(f"#print axioms {t}" for t in THEOREMS) + "\n"
tmp_file = os.path.join(mathlib_dir, "Wave7Agent7Audit.lean")
with open(tmp_file, "w", encoding="utf-8") as f:
    f.write(audit_code)

proc = subprocess.run(
    ["lake", "env", "lean", "-DwarningAsError=true", tmp_file],
    cwd=mathlib_dir,
    capture_output=True,
    text=True,
)
print(proc.stdout)
if proc.stderr:
    print(proc.stderr, file=sys.stderr)
if proc.returncode != 0:
    sys.exit(proc.returncode)

# Collapse wrapped multi-line #print axioms output
normalized = re.sub(r"\n\s+", " ", proc.stdout)
axioms = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", normalized):
    name = m.group(1)
    ax = sorted(a.strip() for a in m.group(2).split(",") if a.strip())
    axioms[name] = ax
for m in re.finditer(r"'([^']+)' does not depend on any axioms", normalized):
    axioms[m.group(1)] = []

for t in THEOREMS:
    if t not in axioms:
        print(f"AUDIT FAIL: missing axiom report for {t}", file=sys.stderr)
        sys.exit(1)
    bad = set(axioms[t]) - ALLOWED_AXIOMS
    if bad:
        print(f"AUDIT FAIL: {t} uses disallowed axioms {bad}", file=sys.stderr)
        sys.exit(1)

res = {
    "status": "PASS",
    "module": "Wave7Agent7ModularAdjustersAndRewiring",
    "audited_theorems": len(THEOREMS),
    "axioms": axioms,
}
os.makedirs(os.path.dirname(OUT_JSON), exist_ok=True)
with open(OUT_JSON, "w", encoding="utf-8") as f:
    json.dump(res, f, indent=2)
print(json.dumps(res, indent=2))
