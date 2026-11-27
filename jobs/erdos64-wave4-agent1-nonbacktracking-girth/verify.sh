#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave4-agent1-nonbacktracking-girth"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base/Shadow.lean" "$work/"
cp "$src/NonBacktrackingGirth.lean" "$work/"
cp "$base/Shadow.lean" "$out/source/"
cp "$src/NonBacktrackingGirth.lean" "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
lake env lean --root="$work" -DwarningAsError=true -o "$work/Shadow.olean" "$work/Shadow.lean" 2>&1 | tee "$out/Shadow.log"
lake env lean --root="$work" -DwarningAsError=true -o "$work/NonBacktrackingGirth.olean" "$work/NonBacktrackingGirth.lean" 2>&1 | tee "$out/NonBacktrackingGirth.log"
python3 "$src/audit.py" "$out" NonBacktrackingGirth
