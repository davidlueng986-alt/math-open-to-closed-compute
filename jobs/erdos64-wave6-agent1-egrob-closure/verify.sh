#!/usr/bin/env bash
set -euo pipefail

echo "Lean version:"
lean --version

LAKE_DIR=/opt/mathlib4
echo "Using Mathlib workspace: ${LAKE_DIR}"

mkdir -p out

lake --dir="${LAKE_DIR}" env lean -DwarningAsError=true jobs/erdos64-wave6-agent1-egrob-closure/Wave6Agent1EGRob3ConnCore.lean 2>&1 | tee out/lean_compile.log

cp jobs/erdos64-wave6-agent1-egrob-closure/Wave6Agent1EGRob3ConnCore.lean out/AuditFile.lean
cat << 'EOF' >> out/AuditFile.lean

#print axioms E64Wave6Agent1.minimal_bad2_no_smaller
#print axioms E64Wave6Agent1.minimal_bad2_no_safe_deletion
#print axioms E64Wave6Agent1.minimal_bad2_no_safe_deletion_disjoint_defects
#print axioms E64Wave6Agent1.minimal_bad2_c4_free
#print axioms E64Wave6Agent1.minimal_bad2_common_neighbors_le_one
#print axioms E64Wave6Agent1.minimal_bad2_common_defect_neighbor_no_high_neighbor
#print axioms E64Wave6Agent1.minimal_bad2_defect_triangle_no_high_neighbor
#print axioms E64Wave6Agent1.minimal_bad2_s2_adjacent_common_high_deg4
#print axioms E64Wave6Agent1.minimal_bad2_v3_density_sharp
#print axioms E64Wave6Agent1.minimal_bad2_trifree_s2_independent
#print axioms E64Wave6Agent1.minimal_bad2_trifree_s1_at_most_one_s2
#print axioms E64Wave6Agent1.minimal_bad2_trifree_v3_density_8_11
#print axioms E64Wave6Agent1.identGraph_cycle_lifts_to_dyadic_path
#print axioms E64Wave6Agent1.minimal_bad2_dist3_all_pairs_dyadic_path
#print axioms E64Wave6Agent1.minimal_bad2_defect_to_any_dyadic_path
#print axioms E64Wave6Agent1.minimal_bad2_non_triangle_edge_dyadic_plus_one_cycle
#print axioms E64Wave6Agent1.minimal_bad2_adjacent_two_vertex_cut_normal_form
#print axioms E64Wave6Agent1.minimal_bad2_two_cut_fermat_disjoint
#print axioms E64Wave6Agent1.eg_rob_3conn_core_sharp_implies_erdos64
EOF

lake --dir="${LAKE_DIR}" env lean -DwarningAsError=true out/AuditFile.lean 2>&1 | tee out/axioms.log

python3 - << 'PY'
import json, re, hashlib

with open("out/axioms.log") as f:
    text = f.read()

pattern = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.MULTILINE | re.DOTALL)
allowed = {"propext", "Classical.choice", "Quot.sound"}
axioms = {}
disallowed = {}
for m in pattern.finditer(text):
    name = m.group(1).strip()
    axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
    axioms[name] = axs
    bad = [a for a in axs if a not in allowed]
    if bad:
        disallowed[name] = bad

with open("jobs/erdos64-wave6-agent1-egrob-closure/Wave6Agent1EGRob3ConnCore.lean", "rb") as f:
    sha = hashlib.sha256(f.read()).hexdigest()

res = {
    "status": "PASS" if (len(axioms) == 19 and not disallowed) else "FAIL",
    "module": "Wave6Agent1EGRob3ConnCore",
    "audited_count": len(axioms),
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
