#!/usr/bin/env bash
set -euo pipefail

echo "Lean version:"
lean --version

LAKE_DIR=""
for d in /opt/mathlib4 /opt/mathlib-workspace /opt/mathlib /opt/lean-workspace /opt/lean /workspace /root/mathlib; do
  if [ -f "$d/lakefile.toml" ] || [ -f "$d/lakefile.lean" ]; then
    LAKE_DIR="$d"
    break
  fi
done
if [ -z "$LAKE_DIR" ]; then
  FOUND=$(find /opt /root -maxdepth 4 \( -name "lakefile.toml" -o -name "lakefile.lean" \) 2>/dev/null | head -n 1 || true)
  if [ -n "$FOUND" ]; then
    LAKE_DIR="$(dirname "$FOUND")"
  fi
fi

JOB_DIR="jobs/erdos64-wave8-agent9-delsarte-sos"
echo "Using Mathlib workspace: ${LAKE_DIR}"
mkdir -p out

# Syntactic hygiene check: reject sorry, admit, axiom, native_decide
for f in Wave8Agent9DelsarteSOS.lean Wave8Agent9TriRewiring.lean; do
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

run_audit Wave8Agent9DelsarteSOS.lean \
  E64Wave8Agent9Delsarte.chebValZ_cast \
  E64Wave8Agent9Delsarte.chebVal_closed \
  E64Wave8Agent9Delsarte.chebMat_comm_A \
  E64Wave8Agent9Delsarte.chebMat_symm \
  E64Wave8Agent9Delsarte.chebMat_rowSum \
  E64Wave8Agent9Delsarte.chebMat_mul \
  E64Wave8Agent9Delsarte.chebMat_mul_any \
  E64Wave8Agent9Delsarte.symm_sq_trace_eq_sum_sq \
  E64Wave8Agent9Delsarte.finset_sq_sum_le_card_mul_sum_sq \
  E64Wave8Agent9Delsarte.clusterSum_sq_div_le \
  E64Wave8Agent9Delsarte.bessel_multi_cluster_sq_trace_ge \
  E64Wave8Agent9Delsarte.single_cluster_sq_trace_ge \
  E64Wave8Agent9Delsarte.sumRangeZ_cast \
  E64Wave8Agent9Delsarte.polyMat_symm \
  E64Wave8Agent9Delsarte.polyMat_rowSum \
  E64Wave8Agent9Delsarte.polyMat_sq_trace_eq \
  E64Wave8Agent9Delsarte.trace_sum_eq_kmDenom_add_walks \
  E64Wave8Agent9Delsarte.delsarte_bessel_unbounded_n_forces_bL \
  E64Wave8Agent9Delsarte.delsarte_two_sq_forces_bL \
  E64Wave8Agent9Delsarte.cubic_cert_forces_bL \
  E64Wave8Agent9Delsarte.cert_girth7_c8_n33 \
  E64Wave8Agent9Delsarte.cert_girth10_c16_n134 \
  E64Wave8Agent9Delsarte.cert_girth10_bip_c16_n201 \
  E64Wave8Agent9Delsarte.cert_girth11_c16_n148 \
  E64Wave8Agent9Delsarte.cert_girth12_c16_n159 \
  E64Wave8Agent9Delsarte.cert_girth12_bip_c16_n239 \
  E64Wave8Agent9Delsarte.cert_girth13_c16_n219 \
  E64Wave8Agent9Delsarte.cert_girth14_c16_n268 \
  E64Wave8Agent9Delsarte.cert_girth14_bip_c16_n346 \
  E64Wave8Agent9Delsarte.cert_girth15_c16_n573

run_audit Wave8Agent9TriRewiring.lean \
  E64Wave8Agent9TriRewiring.tri_rewiring_G0_nonadj_and_disjoint \
  E64Wave8Agent9TriRewiring.tri_rewiring_G0_degree_preserved \
  E64Wave8Agent9TriRewiring.tri_rewiring_G0_girth7_forcing \
  E64Wave8Agent9TriRewiring.tri_rewiring_all_girth11_scale16_rigidity \
  E64Wave8Agent9TriRewiring.repeated_cycle_pow2_forces_pow2_cycle \
  E64Wave8Agent9TriRewiring.cubic_nonsimple_girth7_L16_classification \
  E64Wave8Agent9TriRewiring.cubic_nonsimple_girth15_L32_classification

python3 - << 'PY'
import json, re, hashlib

with open("out/axioms.log") as f:
    text = f.read()

pattern = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.MULTILINE | re.DOTALL)
no_ax_pattern = re.compile(r"'([^']+)' does not depend on any axioms")
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
for m in no_ax_pattern.finditer(text):
    name = m.group(1).strip()
    axioms[name] = []

hashes = {}
for fn in ["Wave8Agent9DelsarteSOS.lean", "Wave8Agent9TriRewiring.lean"]:
    with open(f"jobs/erdos64-wave8-agent9-delsarte-sos/{fn}", "rb") as f:
        hashes[fn] = hashlib.sha256(f.read()).hexdigest()

res = {
    "status": "PASS" if (len(axioms) == 37 and not disallowed) else "FAIL",
    "module": "Wave8Agent9DelsarteSOS_and_TriRewiring",
    "audited_count": len(axioms),
    "expected_count": 37,
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
