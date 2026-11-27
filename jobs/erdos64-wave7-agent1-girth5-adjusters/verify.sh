#!/usr/bin/env bash
set -euo pipefail

JOB_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$JOB_DIR/../.." && pwd)"
OUT_DIR="$ROOT_DIR/out"
mkdir -p "$OUT_DIR"

lean --version

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
SRC="$JOB_DIR/Wave7Agent1Girth5Adjusters.lean"
CHECK_FILE="$OUT_DIR/CheckAxioms.lean"

cp "$SRC" "$OUT_DIR/Wave7Agent1Girth5Adjusters.lean"
cat "$SRC" > "$CHECK_FILE"
cat >> "$CHECK_FILE" << 'EOF'

#print axioms E64Wave7Agent1.maskedSum_of_perm
#print axioms E64Wave7Agent1.brown_unit_perm_complete
#print axioms E64Wave7Agent1.brown_even_perm_complete
#print axioms E64Wave7Agent1.brown_unit_pentagon_gains
#print axioms E64Wave7Agent1.exists_pow2_in_two_octaves_mod3
#print axioms E64Wave7Agent1.mod3_pure_triple_obstruction
#print axioms E64Wave7Agent1.brown_unit_hexagon_halved_gains
#print axioms E64Wave7Agent1.brown_unit_heptagon_gains
#print axioms E64Wave7Agent1.hasPowerCycle_of_perm_brown_unit_necklace
#print axioms E64Wave7Agent1.hasPowerCycle_of_perm_brown_even_necklace
#print axioms E64Wave7Agent1.hasPowerCycle_of_pentagon_necklace
#print axioms E64Wave7Agent1.hasPowerCycle_of_single_unit_pentagon_necklace
#print axioms E64Wave7Agent1.hasPowerCycle_of_hexagon_necklace
#print axioms E64Wave7Agent1.hasPowerCycle_of_heptagon_necklace
#print axioms E64Wave7Agent1.c5_external_neighbors_distinct
#print axioms E64Wave7Agent1.c5_external_no_adjacent_edge
#print axioms E64Wave7Agent1.c5_external_at_most_one_edge
#print axioms E64Wave7Agent1.same_scale_dyadic_plus_one_no_single_edge_overlap
#print axioms E64Wave7Agent1.strict_interior_avoids_seg_edges
#print axioms E64Wave7Agent1.no_hitting_edge_on_strict_interior_adjuster
EOF

(cd "$LAKE_DIR" && lake env lean -DwarningAsError=true "$CHECK_FILE") | tee "$OUT_DIR/lean_axioms.log"
python3 "$JOB_DIR/audit.py" "$OUT_DIR/lean_axioms.log" "$SRC" "$OUT_DIR/verification.json"
