#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
w4a1="$GITHUB_WORKSPACE/jobs/erdos64-wave4-agent1-nonbacktracking-girth"
w5a5="$GITHUB_WORKSPACE/jobs/erdos64-wave5-agent5-girth-tripling"
w5a6="$GITHUB_WORKSPACE/jobs/erdos64-wave5-agent6-chebyshev-girth"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave8-agent2-high-girth"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
for f in \
  "$base/Shadow.lean" \
  "$w4a1/NonBacktrackingGirth.lean" \
  "$w5a5/Wave5Agent5GirthTripling.lean" \
  "$w5a6/Wave5Agent6ChebyshevGirth.lean" \
  "$src/ChebTraceEngine.lean" \
  "$src/NonSimpleHelpers.lean" \
  "$src/NonSimpleDecomp.lean" \
  "$src/NonSimpleBarbell.lean" \
  "$src/NonSimpleTheta.lean" \
  "$src/Wave8Agent2HighGirthClosure.lean"; do
  cp "$f" "$work/"
  cp "$f" "$out/source/"
done
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
for mod in \
  Shadow \
  NonBacktrackingGirth \
  Wave5Agent5GirthTripling \
  Wave5Agent6ChebyshevGirth \
  ChebTraceEngine \
  NonSimpleHelpers \
  NonSimpleDecomp \
  NonSimpleBarbell \
  NonSimpleTheta \
  Wave8Agent2HighGirthClosure; do
  echo "=== Compiling $mod.lean ==="
  lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
python3 "$src/audit.py" "$out" Wave8Agent2HighGirthClosure
