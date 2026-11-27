#!/usr/bin/env bash
set -euo pipefail

JOB_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT_DIR="out"
mkdir -p "$OUT_DIR"

lean --version

# Locate prebuilt Mathlib Lake workspace inside the GHCR Lean container
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
  ls -la /opt || true
  exit 1
fi
echo "Using Mathlib workspace: $MATH_DIR"

# Create audit copy with #print axioms appended
TMP_LEAN="$OUT_DIR/Wave5Agent2EGRobCheck.lean"
cp "$JOB_DIR/Wave5Agent2EGRob.lean" "$TMP_LEAN"
cat >> "$TMP_LEAN" << 'EOF'

#print axioms E64Wave5Agent2EGRob.minimal_bad2_exists
#print axioms E64Wave5Agent2EGRob.minimal_bad2_exact_two_defects
#print axioms E64Wave5Agent2EGRob.minimal_bad2_defects_nonadjacent
#print axioms E64Wave5Agent2EGRob.minimal_bad2_defect_neighbors_cubic
#print axioms E64Wave5Agent2EGRob.minimal_bad2_high_independent
#print axioms E64Wave5Agent2EGRob.minimal_bad2_nonbipartite
#print axioms E64Wave5Agent2EGRob.minimal_bad2_two_edge_connected
#print axioms E64Wave5Agent2EGRob.minimal_bad2_no_cut_vertex
#print axioms E64Wave5Agent2EGRob.minimal_bad2_no_defect_free_two_cut
#print axioms E64Wave5Agent2EGRob.minimal_bad2_no_defect_free_two_vertex_cut
#print axioms E64Wave5Agent2EGRob.eg2_core_completion_three_edge_connected
#print axioms E64Wave5Agent2EGRob.eg2_core_completion_three_connected
#print axioms E64Wave5Agent2EGRob.eg_rob_3conn_core_implies_eg2
#print axioms E64Wave5Agent2EGRob.eg2_implies_eg_rob
#print axioms E64Wave5Agent2EGRob.eg2_iff_eg_rob_3conn_core
#print axioms E64Wave5Agent2EGRob.eg2_iff_eg_rob_3conn
#print axioms E64Wave5Agent2EGRob.eg2_iff_eg_rob_3ec
#print axioms E64Wave5Agent2EGRob.eg_rob_3conn_core_implies_erdos64
#print axioms E64Wave5Agent2EGRob.minimal_bad2_cubic_at_most_two_high_neighbors
#print axioms E64Wave5Agent2EGRob.minimal_bad2_defect_neighbor_at_most_one_high_neighbor
#print axioms E64Wave5Agent2EGRob.minimal_bad2_cubic_density_bound
EOF

# Reject sorry/admit/native_decide/custom axioms syntactically
if grep -En '\b(sorry|admit|axiom|native_decide)\b' "$JOB_DIR/Wave5Agent2EGRob.lean"; then
  echo "ERROR: Forbidden keyword found in Wave5Agent2EGRob.lean"
  exit 1
fi

ABS_TMP="$(cd "$OUT_DIR" && pwd)/Wave5Agent2EGRobCheck.lean"
ABS_LOG="$(cd "$OUT_DIR" && pwd)/lean_axioms.log"

(cd "$MATH_DIR" && lake env lean -DwarningAsError=true "$ABS_TMP") | tee "$ABS_LOG"
python3 "$JOB_DIR/audit.py" "$ABS_LOG" "$OUT_DIR/audit_report.json"
