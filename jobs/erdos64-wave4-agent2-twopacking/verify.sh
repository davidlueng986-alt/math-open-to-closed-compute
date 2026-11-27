#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave4-agent2-twopacking"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base/Shadow.lean" "$base/Core.lean" "$work/"
cp "$src/TwoPackingQuotient.lean" "$work/"
cp "$work/Shadow.lean" "$work/Core.lean" "$work/TwoPackingQuotient.lean" "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
export LEAN_PATH="$work"
for mod in Shadow Core TwoPackingQuotient; do
  lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
python3 "$src/audit.py" "$out/TwoPackingQuotient.log" "$out/axiom-audit.json"
