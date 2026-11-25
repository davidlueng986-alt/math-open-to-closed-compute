#!/usr/bin/env bash
set -euo pipefail
src="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$out/source"
cp "$GITHUB_WORKSPACE/jobs/erdos-64-lean-shadow/Shadow.lean" "$src/"
cp "$GITHUB_WORKSPACE/jobs/erdos-64-lean-descent/Descent.lean" "$src/"
cp "$GITHUB_WORKSPACE/jobs/erdos64-closure-core/"{Core,Leaves}.lean "$src/"
cp "$GITHUB_WORKSPACE/jobs/erdos64-lean-global-pairing/"{BinarySyndrome,PairedShadow,Incidence}.lean "$src/"
cp "$GITHUB_WORKSPACE/jobs/erdos64-closure-leaves/"{BipartiteDegree,TriangleCut}.lean "$src/"
cp "$src/"*.lean "$out/source/"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$src"
for mod in Shadow Core Leaves Descent BinarySyndrome PairedShadow Incidence BipartiteDegree TriangleCut; do
  lake env lean --root="$src" -DwarningAsError=true -o "$src/$mod.olean" "$src/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
failed=0
for mod in ClosedBipartite ClosedTriangle ClosedDefectCore ClosedBipartiteDefect; do
  if ! lake env lean --root="$src" -DwarningAsError=true -o "$src/$mod.olean" "$src/$mod.lean" 2>&1 | tee "$out/$mod.log"; then
    failed=1
  fi
done
test "$failed" -eq 0
lake env lean --root="$src" -DwarningAsError=true -o "$src/Remaining.olean" "$src/Remaining.lean" 2>&1 | tee "$out/Remaining.log"
python3 "$src/audit.py" "$out"
