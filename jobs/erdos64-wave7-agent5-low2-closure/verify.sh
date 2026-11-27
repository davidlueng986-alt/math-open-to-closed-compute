#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
w2="$GITHUB_WORKSPACE/jobs/erdos64-wave2-agent5-lean-weapons"
w3="$GITHUB_WORKSPACE/jobs/erdos64-wave3-agent5-structural"
crit="$GITHUB_WORKSPACE/jobs/erdos64-lean-critical-nov27"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave7-agent5-low2-closure"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base"/{Shadow,Core,Leaves,Descent,PairedShadow,ClosedDefectCore}.lean "$work/"
cp "$w2"/{ConnectivityAndCuts,IdentificationAndContraction}.lean "$work/"
cp "$w3/CutBoundaryWeapons.lean" "$work/"
cp "$crit/MinimalCutCompletion.lean" "$work/"
cp "$src/Wave7Agent5Low2Closure.lean" "$work/"
cp "$src/Wave7Agent5Low2Closure.lean" "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
for mod in Shadow Core Leaves Descent PairedShadow ClosedDefectCore ConnectivityAndCuts IdentificationAndContraction CutBoundaryWeapons MinimalCutCompletion; do
  lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
lake env lean --root="$work" -DwarningAsError=true -o "$work/Wave7Agent5Low2Closure.olean" "$work/Wave7Agent5Low2Closure.lean" 2>&1 | tee "$out/Wave7Agent5Low2Closure.log"
python3 "$src/audit.py" "$out" Wave7Agent5Low2Closure
