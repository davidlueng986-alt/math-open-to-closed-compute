#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave2-agent5-lean-weapons"
build="$GITHUB_WORKSPACE/build_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$build" "$out/source"
cp "$base"/{Shadow,Core,Leaves,Descent,BinarySyndrome,PairedShadow,Incidence,ClosedDefectCore}.lean "$build/"
cp "$src"/*.lean "$build/"
cp "$src"/*.lean "$out/source/"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$build"
for mod in Shadow Core Leaves Descent BinarySyndrome PairedShadow Incidence ClosedDefectCore; do
  lake env lean --root="$build" -DwarningAsError=true -o "$build/$mod.olean" "$build/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
failed=0
for mod in IndependentExpansion ConnectivityAndCuts IdentificationAndContraction; do
  if ! lake env lean --root="$build" -DwarningAsError=true -o "$build/$mod.olean" "$build/$mod.lean" 2>&1 | tee "$out/$mod.log"; then
    failed=1
  fi
done
test "$failed" -eq 0
python3 "$src/audit.py" "$out"
