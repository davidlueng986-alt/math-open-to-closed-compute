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

SRC="jobs/erdos64-wave7-agent10-girth5-detour-rigidity/Erdos64Wave7Agent10.lean"
cp "$SRC" "$LAKE_DIR/Erdos64Wave7Agent10.lean"

cat > "$LAKE_DIR/AuditWave7Agent10.lean" << 'EOF'
import Erdos64Wave7Agent10

#print axioms E64Wave7Agent10.exists_pow2_in_octave
#print axioms E64Wave7Agent10.unit_step_dyadic_hitting
#print axioms E64Wave7Agent10.even_step_dyadic_hitting
#print axioms E64Wave7Agent10.step3_dyadic_hitting
#print axioms E64Wave7Agent10.step3_shifted_dyadic_hitting
#print axioms E64Wave7Agent10.general_step_d_dyadic_hitting
#print axioms E64Wave7Agent10.GeneralDetourChain.cycleVerts_length
#print axioms E64Wave7Agent10.GeneralDetourChain.cycleVerts_nodup
#print axioms E64Wave7Agent10.GeneralDetourChain.toSimpleCycle
#print axioms E64Wave7Agent10.GeneralDetourChain.hasPowerCycle_of_c5_single_edge_detour_chain
#print axioms E64Wave7Agent10.GeneralDetourChain.hasPowerCycle_of_general_step_d_detour_chain
#print axioms E64Wave7Agent10.GeneralDetourChain.strict_interior_detour_robustness
#print axioms E64Wave7Agent10.ThetaOverlap.symmDiffCycle
#print axioms E64Wave7Agent10.ThetaOverlap.symmDiffCycle_length
#print axioms E64Wave7Agent10.same_scale_2k_plus_1_no_single_edge_overlap
#print axioms E64Wave7Agent10.same_scale_2k_plus_1_forbidden_path_overlaps
#print axioms E64Wave7Agent10.same_scale_2k_plus_2_no_P3_overlap
#print axioms E64Wave7Agent10.no_triangle_single_edge_on_2k_minus_1
#print axioms E64Wave7Agent10.no_c5_single_edge_on_2k_minus_3
#print axioms E64Wave7Agent10.c5_no_single_edge_overlap
#print axioms E64Wave7Agent10.c5_no_P4_overlap
#print axioms E64Wave7Agent10.c5_cluster_packing_density_bound
EOF

pushd "$LAKE_DIR" > /dev/null
lake env lean -DwarningAsError=true Erdos64Wave7Agent10.lean
lake env lean -DwarningAsError=true AuditWave7Agent10.lean > /tmp/axioms.txt
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

if len(axioms) != 22:
    raise SystemExit(f"Expected 22 audited declarations, got {len(axioms)}")

sha = hashlib.sha256(open("jobs/erdos64-wave7-agent10-girth5-detour-rigidity/Erdos64Wave7Agent10.lean", "rb").read()).hexdigest()
summary = {
    "status": "PASS",
    "module": "Erdos64Wave7Agent10",
    "theorem_count": len(axioms),
    "axioms": axioms,
    "source_sha256": {"Erdos64Wave7Agent10.lean": sha}
}
with open("out/summary.json", "w") as f:
    json.dump(summary, f, indent=2)
print(json.dumps(summary, indent=2))
PY
