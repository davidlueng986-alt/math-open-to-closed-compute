#!/usr/bin/env bash
set -euo pipefail
src="$GITHUB_WORKSPACE/jobs/jc2-critical-nov28"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$src"/*.lean "$work/"
cp "$src"/*.lean "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
failed=0
for source in "$work"/*.lean; do
  module="$(basename "$source" .lean)"
  if lake env lean --root="$work" -DwarningAsError=true -o "$work/$module.olean" "$source" 2>&1 | tee "$out/$module.log"; then
    :
  else
    failed=1
  fi
done
test "$failed" -eq 0
python3 "$src/audit.py" "$out"
