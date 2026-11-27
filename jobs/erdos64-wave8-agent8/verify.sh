#!/usr/bin/env bash
set -euo pipefail

echo "Lean version:"
lean --version

LAKE_DIR=/opt/mathlib4
echo "Using Mathlib workspace: ${LAKE_DIR}"

mkdir -p out

lake --dir="${LAKE_DIR}" env lean -DwarningAsError=true jobs/erdos64-wave8-agent8/Wave8Agent8GirthFrontier.lean 2>&1 | tee out/lean_compile.log

cp jobs/erdos64-wave8-agent8/Wave8Agent8GirthFrontier.lean out/AuditFile.lean
cat << 'EOF' >> out/AuditFile.lean

#print axioms E64Wave8Agent8.closed_nb_seq_has_simple_cycle_le
#print axioms E64Wave8Agent8.girth9_tailless16_is_simple_cycle
#print axioms E64Wave8Agent8.aeval_chebPoly_eq_chebMat
#print axioms E64Wave8Agent8.nbMat_recurrence
#print axioms E64Wave8Agent8.chebMat_trace_eq_tailless
#print axioms E64Wave8Agent8.sos_trace_lower_bound_general
#print axioms E64Wave8Agent8.sos_trace_lower_bound_bipartite
#print axioms E64Wave8Agent8.cubic_girth_sos_c16
#print axioms E64Wave8Agent8.cubic_bipartite_girth_sos_c16
#print axioms E64Wave8Agent8.cubic_girth9_le_129_has_c16
#print axioms E64Wave8Agent8.cubic_girth10_le_132_has_c16
#print axioms E64Wave8Agent8.cubic_girth11_le_146_has_c16
#print axioms E64Wave8Agent8.cubic_girth12_le_155_has_c16
#print axioms E64Wave8Agent8.cubic_girth13_le_214_has_c16
#print axioms E64Wave8Agent8.cubic_girth14_le_267_has_c16
#print axioms E64Wave8Agent8.cubic_girth15_le_573_has_c16
#print axioms E64Wave8Agent8.cubic_bipartite_girth10_le_259_has_c16
#print axioms E64Wave8Agent8.cubic_bipartite_girth12_le_287_has_c16
#print axioms E64Wave8Agent8.cubic_bipartite_girth14_le_400_has_c16
#print axioms E64Wave8Agent8.four_layer_annulus_telescoping_peak
#print axioms E64Wave8Agent8.subset_interior_boundary_edge_excess
#print axioms E64Wave8Agent8.crossing_ears_seven_cycle_identities
#print axioms E64Wave8Agent8.posa_interlaced_chord_seven_cycles
#print axioms E64Wave8Agent8.k4_subdivision_parity_and_dyadic_sum
EOF

lake --dir="${LAKE_DIR}" env lean -DwarningAsError=true out/AuditFile.lean 2>&1 | tee out/axioms.log

python3 - << 'PY'
import json, re, hashlib

with open("out/axioms.log") as f:
    text = f.read()

pattern = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.MULTILINE | re.DOTALL)
allowed = {"propext", "Classical.choice", "choice", "Quot.sound"}
axioms = {}
disallowed = {}
for m in pattern.finditer(text):
    name = m.group(1).strip()
    axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
    axioms[name] = axs
    bad = [a for a in axs if a not in allowed]
    if bad:
        disallowed[name] = bad

with open("jobs/erdos64-wave8-agent8/Wave8Agent8GirthFrontier.lean", "rb") as f:
    sha = hashlib.sha256(f.read()).hexdigest()

res = {
    "status": "PASS" if (len(axioms) == 24 and not disallowed) else "FAIL",
    "module": "Wave8Agent8GirthFrontier",
    "audited_count": len(axioms),
    "expected_count": 24,
    "disallowed_axioms": disallowed,
    "source_sha256": sha,
    "axioms": axioms,
}
with open("out/verification.json", "w") as f:
    json.dump(res, f, indent=2)
print(json.dumps(res, indent=2))
if res["status"] != "PASS":
    raise SystemExit(1)
PY
