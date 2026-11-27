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

TMP_LEAN="$OUT_DIR/Wave8Agent6Posa2FactorCheck.lean"
cp "$JOB_DIR/Wave8Agent6Posa2Factor.lean" "$TMP_LEAN"
cat >> "$TMP_LEAN" << 'EOF'

#print axioms E64Wave8Agent6.c5_chord_forces_c4
#print axioms E64Wave8Agent6.c5_two_edges_sharing_vertex_forces_c3_or_c4
#print axioms E64Wave8Agent6.c5_split_dichotomy
#print axioms E64Wave8Agent6.two_cycle_double_bridge_four_cycles
#print axioms E64Wave8Agent6.disjoint_c5_double_edge_forces_pow2
#print axioms E64Wave8Agent6.c5_pow2_ring_arithmetic
#print axioms E64Wave8Agent6.c5_ring_realize_simple_cycle
#print axioms E64Wave8Agent6.c5_pow2_ring_forces_pow2_cycle
#print axioms E64Wave8Agent6.cubic_c5_quotient_pow2_cycle_lifts
#print axioms E64Wave8Agent6.minimal_counterexample_no_cubic_c5_quotient_delta3
#print axioms E64Wave8Agent6.c5_factor_minimal_counterexample_impossible
#print axioms E64Wave8Agent6.endpoint_chords_three_cycles
#print axioms E64Wave8Agent6.endpoint_chords_forbid_dyadic_gaps
#print axioms E64Wave8Agent6.posa_pivot_common_neighbor_c4
#print axioms E64Wave8Agent6.posa_pivot_inner_cycles
#print axioms E64Wave8Agent6.posa_pivot_between_cycles
#print axioms E64Wave8Agent6.posa_pivot_beyond_cycles
#print axioms E64Wave8Agent6.crossing_chords_six_cycle_spectrum
#print axioms E64Wave8Agent6.crossing_chords_pow2_forcing
#print axioms E64Wave8Agent6.cubic_shared_vertex_cycles_share_edge
#print axioms E64Wave8Agent6.girth9_closed_walk16_no_split
EOF

if grep -En '\b(sorry|admit|axiom|native_decide)\b' "$JOB_DIR/Wave8Agent6Posa2Factor.lean"; then
  echo "ERROR: Forbidden keyword found in Wave8Agent6Posa2Factor.lean"
  exit 1
fi

ABS_TMP="$(cd "$OUT_DIR" && pwd)/Wave8Agent6Posa2FactorCheck.lean"
ABS_LOG="$(cd "$OUT_DIR" && pwd)/lean_axioms.log"

(cd "$MATH_DIR" && lake env lean -DwarningAsError=true "$ABS_TMP") | tee "$ABS_LOG"
python3 "$JOB_DIR/audit.py" "$ABS_LOG" "$OUT_DIR/audit_report.json"
