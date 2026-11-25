#!/usr/bin/env bash
set -euo pipefail
src="$GITHUB_WORKSPACE/jobs/erdos64-wave2-agent3-structural"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$out/source"
cp "$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves/"{Shadow,Core,Leaves,ClosedDefectCore}.lean "$src/"
cp "$src/"*.lean "$out/source/"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$src"
for mod in Shadow Core Leaves ClosedDefectCore DyadicPaths; do
  lake env lean --root="$src" -DwarningAsError=true -o "$src/$mod.olean" "$src/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
python3 "$src/audit.py" "$out"
