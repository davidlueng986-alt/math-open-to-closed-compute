#!/usr/bin/env bash
set -euo pipefail
src="$GITHUB_WORKSPACE/jobs/erdos64-wave2-agent2-structural"
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$out/source"
work="$(mktemp -d)"
cp "$base/"{Shadow,Core,Leaves,Descent,BinarySyndrome,PairedShadow,Incidence,BipartiteDegree,TriangleCut,ClosedDefectCore}.lean "$work/"
cp "$src/Wave2Structural.lean" "$work/"
cp "$src/Wave2Structural.lean" "$out/source/"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
for mod in Shadow Core Leaves Descent PairedShadow TriangleCut ClosedDefectCore; do
  lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
lake env lean --root="$work" -DwarningAsError=true -o "$work/Wave2Structural.olean" "$work/Wave2Structural.lean" 2>&1 | tee "$out/Wave2Structural.log"
python3 "$src/audit.py" "$out"
