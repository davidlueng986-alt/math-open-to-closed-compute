#!/usr/bin/env bash
set -euo pipefail
task="${1:?pass module name}"
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
src="$GITHUB_WORKSPACE/jobs/erdos64-lean-critical-nov27"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base"/*.lean "$work/"
cp "$GITHUB_WORKSPACE/jobs/erdos64-wave2-agent5-lean-weapons/ConnectivityAndCuts.lean" "$work/"
cp "$GITHUB_WORKSPACE/jobs/erdos64-wave3-agent5-structural/CutBoundaryWeapons.lean" "$work/"
cp "$src"/*.lean "$work/"
cp "$base"/*.lean "$out/source/"
cp "$work/ConnectivityAndCuts.lean" "$work/CutBoundaryWeapons.lean" "$out/source/"
cp "$src"/*.lean "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
case "$task" in
  AllPairsObstruction) deps="Shadow" ;;
  MinimalCutCompletion) deps="Shadow Core Leaves Descent" ;;
  CutCompletionApplication) deps="Shadow Core Leaves Descent PairedShadow ConnectivityAndCuts CutBoundaryWeapons MinimalCutCompletion" ;;
  *) echo "Unknown module: $task" >&2; exit 2 ;;
esac
for mod in $deps; do
  lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
lake env lean --root="$work" -DwarningAsError=true -o "$work/$task.olean" "$work/$task.lean" 2>&1 | tee "$out/$task.log"
python3 "$src/audit.py" "$out" "$task"

if [ "$task" = AllPairsObstruction ]; then
  python3 "$src/verify_witness.py" --output "$out/independent-audit.json"
fi
