#!/usr/bin/env bash
set -euo pipefail

JOB_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$JOB_DIR/../.." && pwd)"
OUT_DIR="$ROOT_DIR/out"
mkdir -p "$OUT_DIR"

lean --version

# Auto-detect pre-built Mathlib project in the container
LAKE_DIR=""
for cand in /opt/lean-project /opt/mathlib /opt/mathlib4 /opt/lean /workspace /root/lean-project; do
  if [ -f "$cand/lakefile.lean" ] || [ -f "$cand/lakefile.toml" ]; then
    LAKE_DIR="$cand"
    break
  fi
done
if [ -z "$LAKE_DIR" ]; then
  LAKE_FILE="$(find /opt / -maxdepth 3 \( -name 'lakefile.lean' -o -name 'lakefile.toml' \) 2>/dev/null | head -n 1 || true)"
  if [ -n "$LAKE_FILE" ]; then
    LAKE_DIR="$(dirname "$LAKE_FILE")"
  fi
fi

echo "Detected LAKE_DIR=$LAKE_DIR"
SRC="$JOB_DIR/Wave6Agent5DyadicNecklaceEGRob.lean"
CHECK_FILE="$OUT_DIR/CheckAxioms.lean"

cp "$SRC" "$OUT_DIR/Wave6Agent5DyadicNecklaceEGRob.lean"
cat "$SRC" > "$CHECK_FILE"
cat >> "$CHECK_FILE" << 'EOF'

#print axioms E64Wave6Agent5.brown_unit_complete
#print axioms E64Wave6Agent5.brown_even_complete
#print axioms E64Wave6Agent5.exists_pow2_in_octave
#print axioms E64Wave6Agent5.exists_subset_sum_pow2_of_brown_unit
#print axioms E64Wave6Agent5.exists_subset_sum_pow2_of_brown_even
#print axioms E64Wave6Agent5.BypassNecklace.necklace_walk_isCycle
#print axioms E64Wave6Agent5.BypassNecklace.cycleWalk_length_decomp
#print axioms E64Wave6Agent5.hasPowerCycle_of_brown_unit_necklace
#print axioms E64Wave6Agent5.hasPowerCycle_of_brown_even_necklace
#print axioms E64Wave6Agent5.hasPowerCycle_of_triangle_necklace
#print axioms E64Wave6Agent5.erdos64_closed_of_brown_necklace_target
#print axioms E64Wave6Agent5.eg2_core_high_edge_avoided
#print axioms E64Wave6Agent5.eg2_core_hitting_edges_in_V3
#print axioms E64Wave6Agent5.eg2_core_high_vertex_forces_two_pow2_cycles
#print axioms E64Wave6Agent5.eg2_core_no_brown_necklace
EOF

(cd "$LAKE_DIR" && lake env lean -DwarningAsError=true "$CHECK_FILE") | tee "$OUT_DIR/lean_axioms.log"
python3 "$JOB_DIR/audit.py" "$OUT_DIR/lean_axioms.log" "$SRC" "$OUT_DIR/verification.json"
