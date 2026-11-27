#!/usr/bin/env bash
set -euo pipefail

echo "Lean version:"
lean --version

LAKE_DIR=/opt/mathlib4
echo "Using Mathlib workspace: ${LAKE_DIR}"

mkdir -p out

lake --dir="${LAKE_DIR}" env lean -DwarningAsError=true jobs/erdos64-wave7-agent2-cycle-overlap/Wave7Agent2CycleOverlap.lean 2>&1 | tee out/lean_compile.log

cp jobs/erdos64-wave7-agent2-cycle-overlap/Wave7Agent2CycleOverlap.lean out/AuditFile.lean
cat << 'EOF' >> out/AuditFile.lean

#print axioms E64Wave7Agent2.same_scale_dyadic_plus_one_no_single_edge_overlap
#print axioms E64Wave7Agent2.same_scale_dyadic_plus_one_path_overlap_exclusion
#print axioms E64Wave7Agent2.mixed_scale_dyadic_plus_one_path_overlap_exclusion
#print axioms E64Wave7Agent2.powerFree_no_c4
#print axioms E64Wave7Agent2.powerFree_no_c8
#print axioms E64Wave7Agent2.c5_overlap_rigidity
#print axioms E64Wave7Agent2.c5_star_obstruction
#print axioms E64Wave7Agent2.theta233_strong_spine_edge_c5_blockade
#print axioms E64Wave7Agent2.theta233_rim_edge_c5_blockade
#print axioms E64Wave7Agent2.cubic_all_c5_refutation
#print axioms E64Wave7Agent2.trifree_minimal_bad2_all_c5_refutation
#print axioms E64Wave7Agent2.minimal_bad2_vge4_dist2_dyadic_path
#print axioms E64Wave7Agent2.minimal_bad2_s0_at_most_two_s2
#print axioms E64Wave7Agent2.minimal_bad2_trifree_adjacent_s1b_forces_c5_deg4
#print axioms E64Wave7Agent2.minimal_bad2_girth6_s1b_independent
#print axioms E64Wave7Agent2.minimal_bad2_girth6_v3_density_20_27
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

with open("jobs/erdos64-wave7-agent2-cycle-overlap/Wave7Agent2CycleOverlap.lean", "rb") as f:
    sha = hashlib.sha256(f.read()).hexdigest()

res = {
    "status": "PASS" if (len(axioms) == 16 and not disallowed) else "FAIL",
    "module": "Wave7Agent2CycleOverlap",
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
