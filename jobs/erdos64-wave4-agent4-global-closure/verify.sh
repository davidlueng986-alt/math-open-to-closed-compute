#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave4-agent4-global-closure"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base"/*.lean "$work/"
cp "$src/UniversalGlobalClosure.lean" "$work/"
cp "$src/UniversalGlobalClosure.lean" "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
export LEAN_PATH="$work"
for mod in Shadow Core Leaves Descent; do
  lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
lake env lean --root="$work" -DwarningAsError=true -o "$work/UniversalGlobalClosure.olean" "$work/UniversalGlobalClosure.lean" 2>&1 | tee "$out/UniversalGlobalClosure.log"
python3 "$src/audit.py" "$out" UniversalGlobalClosure
