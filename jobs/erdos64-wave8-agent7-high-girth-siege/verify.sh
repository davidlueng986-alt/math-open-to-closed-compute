#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
JOB_DIR="$ROOT_DIR/jobs/erdos64-wave8-agent7-high-girth-siege"
OUT_DIR="$ROOT_DIR/out"
mkdir -p "$OUT_DIR"

echo "Lean version:"
lean --version

MATHLIB_DIR="/opt/mathlib4"
echo "Using Mathlib workspace: $MATHLIB_DIR"

SRC="$JOB_DIR/Wave8Agent7HighGirthAndRewiring.lean"
AUDIT_FILE="$OUT_DIR/Wave8Agent7HighGirthAndRewiring_audit.lean"

# Strict syntactic hygiene check: reject sorry, admit, axiom, native_decide
if grep -En '\b(sorry|admit|axiom|native_decide)\b' "$SRC"; then
  echo "ERROR: Forbidden token found in $SRC"
  exit 1
fi

cp "$SRC" "$AUDIT_FILE"
cat >> "$AUDIT_FILE" << 'EOF'

#print axioms E64Wave8Agent7.girth5_edge_external_neighbors_independent
#print axioms E64Wave8Agent7.parallel_rewiring_min_degree_three
#print axioms E64Wave8Agent7.parallel_rewiring_lifting_arithmetic
#print axioms E64Wave8Agent7.chorded_dyadic_plus_two_girth_lower_bound
#print axioms E64Wave8Agent7.chorded_dyadic_plus_two_forbidden_below_girth_threshold
#print axioms E64Wave8Agent7.chorded_dyadic_plus_two_arc_powerfree_obstruction
#print axioms E64Wave8Agent7.powerfree_girth_skips_pow2
#print axioms E64Wave8Agent7.bipartite_powerfree_girth_skips_7_to_10_and_15_to_18
#print axioms E64Wave8Agent7.powerfree_no_repeated_cycle_pow2
#print axioms E64Wave8Agent7.cubic_theta_walk_boundary_rigidity
#print axioms E64Wave8Agent7.cubic_barbell_walk_boundary_rigidity
#print axioms E64Wave8Agent7.cubic_moore_layer_card_bound
#print axioms E64Wave8Agent7.odd_cycle_antipodal_unit_shift
#print axioms E64Wave8Agent7.even_cycle_near_antipodal_two_shift
#print axioms E64Wave8Agent7.high_girth_odd_antipodal_chain_unbounded_closure
#print axioms E64Wave8Agent7.high_girth_even_two_adjuster_chain_unbounded_closure
#print axioms E64Wave8Agent7.odd_cycle_all_ear_shifts_odd
#print axioms E64Wave8Agent7.coprime_shift_frobenius_unbounded_closure
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

for m in re.finditer(r"'([^']+)' does not depend on any axioms", log_text):
    name = m.group(1).strip()
    axioms[name] = []

ok = (len(axioms) == 18) and (len(disallowed) == 0)
res = {
    "status": "PASS" if ok else "FAIL",
    "module": "Wave8Agent7HighGirthAndRewiring",
    "audited_count": len(axioms),
    "expected_count": 18,
    "disallowed_axioms": disallowed,
    "source_sha256": src_sha256,
    "axioms": axioms,
}
with open(out_path, "w", encoding="utf-8") as f:
    json.dump(res, f, indent=2)
print(json.dumps(res, indent=2))
sys.exit(0 if ok else 1)
PY
