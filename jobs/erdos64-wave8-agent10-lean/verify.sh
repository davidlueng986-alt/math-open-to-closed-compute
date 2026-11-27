#!/usr/bin/env bash
set -euo pipefail

mkdir -p out
lean --version

LAKE_DIR=""
for cand in /opt/mathlib4 /opt/lean-project /workspace/mathlib4; do
  if [ -d "$cand" ]; then
    LAKE_DIR="$cand"
    break
  fi
done
echo "Detected LAKE_DIR=$LAKE_DIR"

SRC="jobs/erdos64-wave8-agent10-lean/Erdos64Wave8Agent10.lean"
cp "$SRC" "$LAKE_DIR/Erdos64Wave8Agent10.lean"

cat > "$LAKE_DIR/AuditWave8Agent10.lean" << 'EOF'
import Erdos64Wave8Agent10

#print axioms E64Wave8Agent10.SimpleCycle.ofList
#print axioms E64Wave8Agent10.SimpleCycle.ofTwoArcs
#print axioms E64Wave8Agent10.p3_collapse_double_edge_gives_pow2
#print axioms E64Wave8Agent10.p3_collapse_single_edge_lifts_to_2k_plus_1
#print axioms E64Wave8Agent10.cross_rewiring_single_edge_lifts_to_2k_plus_2
#print axioms E64Wave8Agent10.cross_rewiring_crossed_pair_lifts_to_2k_plus_2
#print axioms E64Wave8Agent10.cross_rewiring_no_disjoint_pair_below_2g_minus_2
#print axioms E64Wave8Agent10.cross_rewiring_girth10_eliminates_c4_c8_c16_pairs
#print axioms E64Wave8Agent10.same_side_suppression_lifts_to_2k_plus_1_or_2
#print axioms E64Wave8Agent10.CrossingChordPair.outerCycle_len
#print axioms E64Wave8Agent10.CrossingChordPair.chord1CycleA_len
#print axioms E64Wave8Agent10.CrossingChordPair.chord1CycleB_len
#print axioms E64Wave8Agent10.CrossingChordPair.chord2CycleA_len
#print axioms E64Wave8Agent10.CrossingChordPair.chord2CycleB_len
#print axioms E64Wave8Agent10.CrossingChordPair.crossCycleA_len
#print axioms E64Wave8Agent10.CrossingChordPair.crossCycleB_len
#print axioms E64Wave8Agent10.crossing_chords_seven_cycle_spectrum
#print axioms E64Wave8Agent10.crossing_chords_balanced_sum_refutation
#print axioms E64Wave8Agent10.RungLadder.windowCycle_len
#print axioms E64Wave8Agent10.ladder_girth_mod4_two_immunity
#print axioms E64Wave8Agent10.ladder_girth10_mod8_shift_immunity
#print axioms E64Wave8Agent10.ladder_girth5_closure
#print axioms E64Wave8Agent10.ladder_girth7_closure
#print axioms E64Wave8Agent10.ladder_girth9_closure
#print axioms E64Wave8Agent10.ladder_girth11_closure
#print axioms E64Wave8Agent10.ladder_girth12_closure
#print axioms E64Wave8Agent10.ladder_girth13_closure
#print axioms E64Wave8Agent10.twisted_ladder_breaks_mod4_two_barrier
#print axioms E64Wave8Agent10.ihara_chebyshev_b16_cage_thresholds
#print axioms E64Wave8Agent10.egrob_two_copy_gluing_no_half_pow2_path
EOF

pushd "$LAKE_DIR" > /dev/null
lake env lean -DwarningAsError=true Erdos64Wave8Agent10.lean
lake env lean -DwarningAsError=true AuditWave8Agent10.lean > /tmp/axioms.txt
popd > /dev/null

cat /tmp/axioms.txt
cp /tmp/axioms.txt out/axioms.txt

python3 - << 'PY'
import json, hashlib, re

with open("out/axioms.txt") as f:
    text = f.read()

axioms = {}
allowed = {"propext", "Classical.choice", "Quot.sound"}
for line in text.splitlines():
    m = re.match(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line.strip())
    if m:
        name = m.group(1)
        ax_list = [a.strip() for a in m.group(2).split(",") if a.strip()]
        for a in ax_list:
            if a not in allowed:
                raise SystemExit(f"FORBIDDEN AXIOM {a} in {name}")
        axioms[name] = sorted(ax_list)

if len(axioms) != 30:
    raise SystemExit(f"Expected 30 audited declarations, got {len(axioms)}")

sha = hashlib.sha256(open("jobs/erdos64-wave8-agent10-lean/Erdos64Wave8Agent10.lean", "rb").read()).hexdigest()
summary = {
    "status": "PASS",
    "module": "Erdos64Wave8Agent10",
    "theorem_count": len(axioms),
    "axioms": axioms,
    "source_sha256": {"Erdos64Wave8Agent10.lean": sha}
}
with open("out/summary.json", "w") as f:
    json.dump(summary, f, indent=2)
print(json.dumps(summary, indent=2))
PY
