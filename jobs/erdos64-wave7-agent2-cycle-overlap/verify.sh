#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
JOB_DIR="$ROOT_DIR/jobs/erdos64-wave7-agent2-cycle-overlap"
OUT_DIR="$ROOT_DIR/out"
mkdir -p "$OUT_DIR"

echo "Lean version:"
lean --version

MATHLIB_DIR="/opt/mathlib4"
echo "Using Mathlib workspace: $MATHLIB_DIR"

SRC="$JOB_DIR/Wave7Agent2CycleOverlap.lean"
AUDIT_FILE="$OUT_DIR/Wave7Agent2CycleOverlap_audit.lean"

cp "$SRC" "$AUDIT_FILE"
cat >> "$AUDIT_FILE" << 'EOF'

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

cd "$MATHLIB_DIR"
lake env lean -DwarningAsError=true "$SRC" 2>&1 | tee "$OUT_DIR/lean_compile.log"
lake env lean -DwarningAsError=true "$AUDIT_FILE" 2>&1 | tee "$OUT_DIR/lean_axioms.log"

python3 - "$SRC" "$OUT_DIR/lean_axioms.log" "$OUT_DIR/verification.json" << 'PY'
import hashlib, json, re, sys

src_path, log_path, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
with open(src_path, "rb") as f:
    src_sha256 = hashlib.sha256(f.read()).hexdigest()

with open(log_path, "r", encoding="utf-8") as f:
    log_text = f.read()

allowed = {"propext", "Classical.choice", "choice", "Quot.sound"}
axioms = {}
disallowed = {}

for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log_text):
    name = m.group(1).strip()
    ax_list = [a.strip() for a in m.group(2).split(",") if a.strip()]
    axioms[name] = ax_list
    bad = [a for a in ax_list if a not in allowed]
    if bad:
        disallowed[name] = bad

ok = (len(axioms) == 16) and (len(disallowed) == 0)
res = {
    "status": "PASS" if ok else "FAIL",
    "module": "Wave7Agent2CycleOverlap",
    "audited_count": len(axioms),
    "disallowed_axioms": disallowed,
    "source_sha256": src_sha256,
    "axioms": axioms,
}
with open(out_path, "w", encoding="utf-8") as f:
    json.dump(res, f, indent=2)
print(json.dumps(res, indent=2))
sys.exit(0 if ok else 1)
PY
