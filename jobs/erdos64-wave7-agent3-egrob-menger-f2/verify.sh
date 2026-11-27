#!/usr/bin/env bash
set -uo pipefail

echo "Lean version:"
lean --version

LAKE_DIR=/opt/mathlib4
JOB_DIR=jobs/erdos64-wave7-agent3-egrob-menger-f2
echo "Using Mathlib workspace: ${LAKE_DIR}"

mkdir -p out

# Syntactic hygiene check: reject sorry, admit, axiom, native_decide
for f in Pillar1Menger.lean Pillar2Tutte.lean Pillar3F2Parity.lean Pillar4Triangles.lean; do
  if grep -En '\b(sorry|admit|axiom|native_decide)\b' "${JOB_DIR}/${f}"; then
    echo "ERROR: Forbidden token found in ${f}"
    exit 1
  fi
done

rm -f out/axioms.log
touch out/axioms.log
FAIL=0

run_audit() {
  local fname="$1"
  shift
  echo "=== Compiling ${fname} ==="
  if lake --dir="${LAKE_DIR}" env lean -DwarningAsError=true "${JOB_DIR}/${fname}" 2>&1 | tee "out/${fname}.compile.log"; then
    cp "${JOB_DIR}/${fname}" "out/Audit_${fname}"
    for thm in "$@"; do
      echo "#print axioms ${thm}" >> "out/Audit_${fname}"
    done
    if ! lake --dir="${LAKE_DIR}" env lean -DwarningAsError=true "out/Audit_${fname}" 2>&1 | tee -a out/axioms.log; then
      FAIL=1
    fi
  else
    FAIL=1
  fi
}

run_audit Pillar1Menger.lean \
  E64Wave7Agent3P1.minimal_bad2_two_cut_avoids_defects \
  E64Wave7Agent3P1.minimal_bad2_two_cut_exact_two_components \
  E64Wave7Agent3P1.minimal_bad2_menger_separator_forces_defect_split \
  E64Wave7Agent3P1.minimal_bad2_two_cut_dyadic_path_disjoint

run_audit Pillar2Tutte.lean \
  E64Wave7Agent3P2.minimal_bad2_nonadj_two_cut_torso_fermat_path \
  E64Wave7Agent3P2.minimal_bad2_nonadj_two_cut_one_sided_cubic \
  E64Wave7Agent3P2.minimal_bad2_nonadj_two_cut_contraction_dyadic_path \
  E64Wave7Agent3P2.minimal_bad2_nonadj_two_cut_scale_asymmetry \
  E64Wave7Agent3P2.minimal_bad2_defect_nonadj_neighbors_dual_cycles

run_audit Pillar3F2Parity.lean \
  E64Wave7Agent3P3.powerfree_theta_dyadic_sum_exclusion \
  E64Wave7Agent3P3.powerfree_f2_same_scale_cycle_overlap_exclusion \
  E64Wave7Agent3P3.powerfree_chord_arc_exclusion \
  E64Wave7Agent3P3.powerfree_triangle_fermat_edge_exclusion \
  E64Wave7Agent3P3.powerfree_triangle_dyadic_plus_one_two_edge_exclusion \
  E64Wave7Agent3P3.minimal_bad2_f2_cycle_space_dim_lower_bound

run_audit Pillar4Triangles.lean \
  E64Wave7Agent3P4.minimal_bad2_high_apex_triangle_base_dyadic_plus_one_cycle \
  E64Wave7Agent3P4.minimal_bad2_cubic_triangle_external_not_all_high \
  E64Wave7Agent3P4.minimal_bad2_cubic_triangle_dual_cycle_lifting

if [ "${FAIL}" -ne 0 ]; then
  echo "One or more Lean modules failed to compile."
  exit 1
fi

python3 - << 'PY'
import json, re, hashlib

with open("out/axioms.log") as f:
    text = f.read()

pattern = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.MULTILINE | re.DOTALL)
allowed = {"propext", "Classical.choice", "Quot.sound"}
axioms = {}
disallowed = {}
for m in pattern.finditer(text):
    name = m.group(1).strip()
    axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
    axioms[name] = axs
    bad = [a for a in axs if a not in allowed]
    if bad:
        disallowed[name] = bad

hashes = {}
for fn in ["Pillar1Menger.lean", "Pillar2Tutte.lean", "Pillar3F2Parity.lean", "Pillar4Triangles.lean"]:
    with open(f"jobs/erdos64-wave7-agent3-egrob-menger-f2/{fn}", "rb") as f:
        hashes[fn] = hashlib.sha256(f.read()).hexdigest()

res = {
    "status": "PASS" if (len(axioms) == 18 and not disallowed) else "FAIL",
    "module": "Wave7Agent3EGRob3Conn",
    "audited_count": len(axioms),
    "expected_count": 18,
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
