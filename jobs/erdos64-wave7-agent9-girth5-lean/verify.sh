#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="$(pwd)/out"
mkdir -p "$OUT_DIR"

# Locate prebuilt Mathlib workspace in the GHCR Lean 4.36.0 container
MATHLIB_DIR=""
for d in /opt/mathlib-workspace /opt/mathlib4 /opt/mathlib /opt/lean-workspace /opt/lean /workspace /root/mathlib; do
  if [ -f "$d/lakefile.toml" ] || [ -f "$d/lakefile.lean" ]; then
    MATHLIB_DIR="$d"
    break
  fi
done
if [ -z "$MATHLIB_DIR" ]; then
  FOUND=$(find /opt /root -maxdepth 4 \( -name "lakefile.toml" -o -name "lakefile.lean" \) 2>/dev/null | head -n 1 || true)
  if [ -n "$FOUND" ]; then
    MATHLIB_DIR="$(dirname "$FOUND")"
  fi
fi

echo "Detected MATHLIB_DIR=$MATHLIB_DIR"
lean --version

# Create audit file checking all 18 theorems and printing transitive axioms
cat > "$OUT_DIR/AuditWave7Agent9.lean" << 'EOF'
import Wave7Agent9Girth5Theory

#print axioms E64Wave7Agent9.pow2_in_interval_of_double_sub_one
#print axioms E64Wave7Agent9.pow2_even_in_interval_of_double_sub_two
#print axioms E64Wave7Agent9.absSum_eq_posSum_add_negSum
#print axioms E64Wave7Agent9.signed_adjuster_normalization
#print axioms E64Wave7Agent9.signed_double_shortcut_threshold
#print axioms E64Wave7Agent9.brown_subset_sum_complete
#print axioms E64Wave7Agent9.signed_adjuster_brown_pow2
#print axioms E64Wave7Agent9.parity_flip_even_brown_pow2
#print axioms E64Wave7Agent9.modular_dyadic_ap_hit_canon
#print axioms E64Wave7Agent9.mod3_dyadic_ap_hit
#print axioms E64Wave7Agent9.mod5_dyadic_ap_hit
#print axioms E64Wave7Agent9.cubic_shared_vertex_forces_shared_edge
#print axioms E64Wave7Agent9.same_scale_pow2_plus_one_no_single_edge
#print axioms E64Wave7Agent9.same_scale_pow2_plus_one_forbidden_path
#print axioms E64Wave7Agent9.same_scale_pow2_plus_two_no_single_p3
#print axioms E64Wave7Agent9.cross_scale_pow2_plus_one_forbidden_path
#print axioms E64Wave7Agent9.pentagon_no_p4_overlap_with_pow2_plus_one
#print axioms E64Wave7Agent9.pentagon_overlap_only_p3
#print axioms E64Wave7Agent9.pentagon_density_bound_of_cluster_isolation
EOF

cp "$SCRIPT_DIR/Wave7Agent9Girth5Theory.lean" "$MATHLIB_DIR/Wave7Agent9Girth5Theory.lean"
cp "$OUT_DIR/AuditWave7Agent9.lean" "$MATHLIB_DIR/AuditWave7Agent9.lean"

cd "$MATHLIB_DIR"
lake env lean -DwarningAsError=true -o "$OUT_DIR/Wave7Agent9Girth5Theory.olean" Wave7Agent9Girth5Theory.lean
LEAN_PATH="$OUT_DIR:$(lake env printenv LEAN_PATH)" lake env lean -DwarningAsError=true AuditWave7Agent9.lean | tee "$OUT_DIR/axioms.log"

# Verify zero sorryAx and zero native_decide / Lean.ofReduceBool
if grep -qE "sorryAx|ofReduceBool|trustCompiler" "$OUT_DIR/axioms.log"; then
  echo "ERROR: Forbidden axiom detected!"
  exit 1
fi

echo "PASS: All 19 audited theorems in Wave7Agent9Girth5Theory verified cleanly with standard axioms only."
