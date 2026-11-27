#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
w6="$GITHUB_WORKSPACE/jobs/erdos64-wave6-agent2-tseg-lean"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave7-agent4-tseg-lean"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base/Shadow.lean" "$work/"
cp "$w6/Wave6Agent2TSEG.lean" "$work/"
cp "$src/Wave7Agent4TSEG.lean" "$work/"
cp "$work"/*.lean "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
lake env lean --root="$work" -DwarningAsError=true -o "$work/Shadow.olean" "$work/Shadow.lean" 2>&1 | tee "$out/Shadow.log"
lake env lean --root="$work" -DwarningAsError=true -o "$work/Wave6Agent2TSEG.olean" "$work/Wave6Agent2TSEG.lean" 2>&1 | tee "$out/Wave6Agent2TSEG.log"
lake env lean --root="$work" -DwarningAsError=true -o "$work/Wave7Agent4TSEG.olean" "$work/Wave7Agent4TSEG.lean" 2>&1 | tee "$out/Wave7Agent4TSEG.log"
python3 "$src/audit.py" "$out" Wave7Agent4TSEG
