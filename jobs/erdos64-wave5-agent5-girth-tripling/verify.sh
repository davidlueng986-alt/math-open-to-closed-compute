#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
w4a1="$GITHUB_WORKSPACE/jobs/erdos64-wave4-agent1-nonbacktracking-girth"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave5-agent5-girth-tripling"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base/Shadow.lean" "$work/"
cp "$w4a1/NonBacktrackingGirth.lean" "$work/"
cp "$src/Wave5Agent5GirthTripling.lean" "$work/"
cp "$work"/*.lean "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
lake env lean --root="$work" -DwarningAsError=true -o "$work/Shadow.olean" "$work/Shadow.lean" 2>&1 | tee "$out/Shadow.log"
lake env lean --root="$work" -DwarningAsError=true -o "$work/NonBacktrackingGirth.olean" "$work/NonBacktrackingGirth.lean" 2>&1 | tee "$out/NonBacktrackingGirth.log"
lake env lean --root="$work" -DwarningAsError=true -o "$work/Wave5Agent5GirthTripling.olean" "$work/Wave5Agent5GirthTripling.lean" 2>&1 | tee "$out/Wave5Agent5GirthTripling.log"
python3 "$src/audit.py" "$out" Wave5Agent5GirthTripling
