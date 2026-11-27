#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave4-agent6-global-closure"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base"/*.lean "$work/"
cp "$GITHUB_WORKSPACE/jobs/erdos64-wave2-agent5-lean-weapons/ConnectivityAndCuts.lean" "$work/"
cp "$GITHUB_WORKSPACE/jobs/erdos64-wave3-agent5-structural/CutBoundaryWeapons.lean" "$work/"
cp "$GITHUB_WORKSPACE/jobs/erdos64-lean-critical-nov27/MinimalCutCompletion.lean" "$work/"
cp "$GITHUB_WORKSPACE/jobs/erdos64-lean-critical-nov27/CutCompletionApplication.lean" "$work/"
cp "$src"/Wave4Agent6GlobalClosure.lean "$work/"
cp "$work"/*.lean "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
deps="Shadow Core Leaves Descent BinarySyndrome BipartiteDegree PairedShadow Incidence TriangleCut ClosedBipartite ClosedBipartiteDefect ClosedDefectCore ClosedTriangle Remaining ConnectivityAndCuts CutBoundaryWeapons MinimalCutCompletion CutCompletionApplication"
for mod in $deps; do
  lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
lake env lean --root="$work" -DwarningAsError=true -o "$work/Wave4Agent6GlobalClosure.olean" "$work/Wave4Agent6GlobalClosure.lean" 2>&1 | tee "$out/Wave4Agent6GlobalClosure.log"
python3 "$src/audit.py" "$out" Wave4Agent6GlobalClosure
