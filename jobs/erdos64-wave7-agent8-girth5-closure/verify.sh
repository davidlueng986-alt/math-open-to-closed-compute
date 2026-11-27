#!/usr/bin/env bash
set -euo pipefail

JOB_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="out"
mkdir -p "$OUT_DIR"

lean --version

MATH_DIR=""
for cand in /opt/mathlib /opt/lean /opt/math-project /opt/lean-project /opt/mathlib4 /workspace; do
  if [ -f "$cand/lakefile.toml" ] || [ -f "$cand/lakefile.lean" ]; then
    MATH_DIR="$cand"
    break
  fi
done
if [ -z "$MATH_DIR" ]; then
  LAKEFILE="$(find /opt /root /home -maxdepth 4 \( -name lakefile.toml -o -name lakefile.lean \) 2>/dev/null | head -n 1 || true)"
  if [ -n "$LAKEFILE" ]; then
    MATH_DIR="$(dirname "$LAKEFILE")"
  fi
fi
if [ -z "$MATH_DIR" ]; then
  echo "ERROR: Could not locate Mathlib Lake workspace in container"
  exit 1
fi
echo "Using Mathlib workspace: $MATH_DIR"

TMP_LEAN="$OUT_DIR/Wave7Agent8Girth5ClosureCheck.lean"
cp "$JOB_DIR/Wave7Agent8Girth5Closure.lean" "$TMP_LEAN"
cat >> "$TMP_LEAN" << 'EOF'

#print axioms E64Wave7Agent8.pentagram_p3_closes_c8
#print axioms E64Wave7Agent8.pentagram_cover_forces_p3
#print axioms E64Wave7Agent8.c5_star_covered_has_c8
#print axioms E64Wave7Agent8.c5_external_neighbors_distinct_of_girth5
#print axioms E64Wave7Agent8.c5_star_covered_girth5_has_pow2_cycle
#print axioms E64Wave7Agent8.two_paths_form_simple_cycle
#print axioms E64Wave7Agent8.same_scale_fermat_no_single_edge_overlap
#print axioms E64Wave7Agent8.same_scale_fermat_forbidden_overlaps
#print axioms E64Wave7Agent8.cross_scale_fermat_forbidden_overlap
#print axioms E64Wave7Agent8.disjoint_fermat_two_bridge_sum_obstruction
#print axioms E64Wave7Agent8.disjoint_fermat_two_bridge_diff3_obstruction
#print axioms E64Wave7Agent8.odd_cycle_adjuster_realizes_unit_interval
#print axioms E64Wave7Agent8.odd_cycle_adjuster_necklace_closes_pow2
#print axioms E64Wave7Agent8.even_cycle_adjuster_realizes_even_interval
#print axioms E64Wave7Agent8.even_cycle_adjuster_necklace_closes_pow2
EOF

if grep -En '\b(sorry|admit|axiom|native_decide)\b' "$JOB_DIR/Wave7Agent8Girth5Closure.lean"; then
  echo "ERROR: Forbidden keyword found in Wave7Agent8Girth5Closure.lean"
  exit 1
fi

ABS_TMP="$(cd "$OUT_DIR" && pwd)/Wave7Agent8Girth5ClosureCheck.lean"
ABS_LOG="$(cd "$OUT_DIR" && pwd)/lean_axioms.log"

(cd "$MATH_DIR" && lake env lean -DwarningAsError=true "$ABS_TMP") | tee "$ABS_LOG"
python3 "$JOB_DIR/audit.py" "$ABS_LOG" "$OUT_DIR/audit_report.json"
