#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(pwd)"
JOB_DIR="${REPO_ROOT}/jobs/erdos64-wave5-agent1-eg2core"
OUT_DIR="${REPO_ROOT}/out"
mkdir -p "${OUT_DIR}"

git -c safe.directory="*" rev-parse HEAD | tee "${OUT_DIR}/source_commit.txt"

LAKE_DIR=""
for cand in /opt/mathlib4 /opt/mathlib-project /opt/lean-project /opt/mathlib /workspace; do
  if [ -f "${cand}/lakefile.lean" ] || [ -f "${cand}/lakefile.toml" ]; then
    LAKE_DIR="${cand}"
    break
  fi
done
if [ -z "${LAKE_DIR}" ]; then
  echo "ERROR: Could not locate Mathlib lake project directory" >&2
  exit 1
fi
echo "Using LAKE_DIR=${LAKE_DIR}"

if [ -d "${LAKE_DIR}/.git" ]; then
  git -c safe.directory="*" -C "${LAKE_DIR}" rev-parse HEAD | tee "${OUT_DIR}/mathlib_commit.txt"
elif [ -d "${LAKE_DIR}/.lake/packages/mathlib/.git" ]; then
  git -c safe.directory="*" -C "${LAKE_DIR}/.lake/packages/mathlib" rev-parse HEAD | tee "${OUT_DIR}/mathlib_commit.txt"
else
  echo "unknown" | tee "${OUT_DIR}/mathlib_commit.txt"
fi

lean --version | tee "${OUT_DIR}/lean_version.txt"

cp "${JOB_DIR}/Wave5Agent1EG2Core.lean" "${LAKE_DIR}/Wave5Agent1EG2Core.lean"
cp "${JOB_DIR}/Wave5Agent1EG2Core.lean" "${OUT_DIR}/Wave5Agent1EG2Core.lean"

cat > "${LAKE_DIR}/AuditWave5Agent1.lean" << 'EOF'
import Wave5Agent1EG2Core

#print axioms E64Wave5Agent1EG2Core.minimal_bad2_connected
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_two_edge_connected
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_two_connected
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_two_cut_normal_form
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_v3_component_high_bottleneck
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_no_v3_all_high_neighbors
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_no_adjacent_two_high_disjoint
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_defect_neighbor_at_most_one_high
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_c4_free
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_v3_density_two_thirds
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_defect_dyadic_path
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_defect_pair_contraction_edge_robust
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_defect_pair_contraction_neighbor_robust
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_delete_defect_nonbipartite
#print axioms E64Wave5Agent1EG2Core.minimal_bad2_odd_edge_transversal_constraints
EOF

pushd "${LAKE_DIR}" >/dev/null
lake env lean -DwarningAsError=true -o "${LAKE_DIR}/Wave5Agent1EG2Core.olean" "${LAKE_DIR}/Wave5Agent1EG2Core.lean"
LEAN_PATH="${LAKE_DIR}:$(lake env printenv LEAN_PATH)" lake env lean -DwarningAsError=true "${LAKE_DIR}/AuditWave5Agent1.lean" | tee "${OUT_DIR}/axioms.txt"
popd >/dev/null

python3 "${JOB_DIR}/audit.py" "${OUT_DIR}" | tee "${OUT_DIR}/verification.json"
