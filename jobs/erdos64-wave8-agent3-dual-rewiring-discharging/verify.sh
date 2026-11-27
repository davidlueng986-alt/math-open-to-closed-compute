#!/usr/bin/env bash
set -euo pipefail

echo "Lean version:"
lean --version

LAKE_DIR=/opt/mathlib4
JOB_DIR=jobs/erdos64-wave8-agent3-dual-rewiring-discharging
echo "Using Mathlib workspace: ${LAKE_DIR}"

mkdir -p out

# Syntactic hygiene check: reject sorry, admit, axiom, native_decide
for f in Part1DualCrossRewiring.lean Part2GlobalDischarging.lean Part3TutteCleavageCoupling.lean; do
  if grep -En '\b(sorry|admit|axiom|native_decide)\b' "${JOB_DIR}/${f}"; then
    echo "ERROR: Forbidden token found in ${f}"
    exit 1
  fi
done

rm -f out/axioms.log
touch out/axioms.log

run_audit() {
  local fname="$1"
  shift
  echo "=== Compiling ${fname} ==="
  lake --dir="${LAKE_DIR}" env lean -DwarningAsError=true "${JOB_DIR}/${fname}" 2>&1 | tee "out/${fname}.compile.log"
  cp "${JOB_DIR}/${fname}" "out/Audit_${fname}"
  for thm in "$@"; do
    echo "#print axioms ${thm}" >> "out/Audit_${fname}"
  done
  lake --dir="${LAKE_DIR}" env lean -DwarningAsError=true "out/Audit_${fname}" 2>&1 | tee -a out/axioms.log
}

run_audit Part1DualCrossRewiring.lean \
  E64Wave8Agent3P1.crossRewire_exact_degree_eq \
  E64Wave8Agent3P1.crossRewire_preserves_defects \
  E64Wave8Agent3P1.minimal_bad2_dual_cross_rewiring_both_pow2 \
  E64Wave8Agent3P1.crossRewire_single_edge_lifts_to_cycle_plus_two \
  E64Wave8Agent3P1.crossRewire_twisted_double_lifts_three_cycles \
  E64Wave8Agent3P1.crossRewire_parallel_double_lifts_dumbbell \
  E64Wave8Agent3P1.dual_cross_rewiring_girth_double_cross_bounds \
  E64Wave8Agent3P1.dual_cross_rewiring_same_scale_L1_must_intersect

run_audit Part2GlobalDischarging.lean \
  E64Wave8Agent3P2.minimal_bad2_vge4_independent \
  E64Wave8Agent3P2.minimal_bad2_v3_no_all_high_neighbors \
  E64Wave8Agent3P2.minimal_bad2_v3_component_size_ge_girth_sub_one \
  E64Wave8Agent3P2.minimal_bad2_girth_g_v3_density_universal \
  E64Wave8Agent3P2.minimal_bad2_girth7_v3_density_3_4 \
  E64Wave8Agent3P2.minimal_bad2_girth8_auto_girth9_v3_density_16_21 \
  E64Wave8Agent3P2.minimal_bad2_girth_g_v3_internal_degree_bound

run_audit Part3TutteCleavageCoupling.lean \
  E64Wave8Agent3P3.dual_cross_rewiring_trifree_same_scale_c6_rigidity \
  E64Wave8Agent3P3.minimal_bad2_v3_min_component_forces_vge4_girth_cycle \
  E64Wave8Agent3P3.crossRewire_preserves_two_cut_separation \
  E64Wave8Agent3P3.crossRewire_two_cut_dyadic_path_asymmetry

python3 - << 'PY'
import json, re, hashlib

with open("out/axioms.log") as f:
    text = f.read()

pattern = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.MULTILINE | re.DOTALL)
pattern0 = re.compile(r"'([^']+)' does not depend on any axioms", re.MULTILINE)
allowed = {"propext", "Classical.choice", "choice", "Quot.sound"}
axioms = {}
disallowed = {}
for m in pattern.finditer(text):
    name = m.group(1).strip()
    axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
    axioms[name] = axs
    bad = [a for a in axs if a not in allowed]
    if bad:
        disallowed[name] = bad
for m in pattern0.finditer(text):
    name = m.group(1).strip()
    axioms[name] = []

hashes = {}
for fn in ["Part1DualCrossRewiring.lean", "Part2GlobalDischarging.lean", "Part3TutteCleavageCoupling.lean"]:
    with open(f"jobs/erdos64-wave8-agent3-dual-rewiring-discharging/{fn}", "rb") as f:
        hashes[fn] = hashlib.sha256(f.read()).hexdigest()

res = {
    "status": "PASS" if (len(axioms) == 19 and not disallowed) else "FAIL",
    "module": "Wave8Agent3DualRewiringAndDischarging",
    "audited_count": len(axioms),
    "expected_count": 19,
    "disallowed_axioms": disallowed,
    "source_sha256": hashes,
    "axioms": axioms,
}
with open("out/verification.json", "w") as f:
    json.dump(res, f, indent=2)
print(json.dumps(res, indent=2))
if res["status"] != "PASS":
    raise SystemExit(1)
PY
