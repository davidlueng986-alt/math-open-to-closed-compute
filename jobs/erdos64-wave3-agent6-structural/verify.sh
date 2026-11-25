#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
w2="$GITHUB_WORKSPACE/jobs/erdos64-wave2-agent6-structural"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave3-agent6-structural"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base"/*.lean "$work/"
cp "$w2/Identification.lean" "$work/"
cp "$src"/*.lean "$work/"
cp "$src"/*.lean "$out/source/"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
for mod in Shadow Core Leaves Descent BinarySyndrome PairedShadow Incidence BipartiteDegree TriangleCut ClosedDefectCore Identification; do
  lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
failed=0
for mod in GeneralInvolution P3AndDefectForcing CutObstructions TriangleCoverContraction; do
  if ! lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"; then
    failed=1
  fi
done
test "$failed" -eq 0
python3 "$src/audit.py" "$out"
