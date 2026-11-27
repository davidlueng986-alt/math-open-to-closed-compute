#!/usr/bin/env bash
set -euo pipefail
base="$GITHUB_WORKSPACE/jobs/erdos64-complete-leaves"
src="$GITHUB_WORKSPACE/jobs/erdos64-wave4-agent3-lean"
work="$GITHUB_WORKSPACE/work_lean"
out="$GITHUB_WORKSPACE/out"
mkdir -p "$work" "$out/source"
cp "$base/Shadow.lean" "$base/Core.lean" "$work/"
cp "$src/Wave4Agent3GlobalClosure.lean" "$work/"
cp "$work"/*.lean "$out/source/"
printf '%s\n' "$GITHUB_SHA" | tee "$out/source-commit.txt"
cd /opt/mathlib4
git rev-parse HEAD | tee "$out/mathlib-commit.txt"
lake env lean --version | tee "$out/lean-version.txt"
test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
export LEAN_PATH="$work"
for mod in Shadow Core Wave4Agent3GlobalClosure; do
  lake env lean --root="$work" -DwarningAsError=true -o "$work/$mod.olean" "$work/$mod.lean" 2>&1 | tee "$out/$mod.log"
done
python3 - << 'EOF'
import json, pathlib, re, sys
out = pathlib.Path("/github/workspace/out") if pathlib.Path("/github/workspace/out").exists() else pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else None
EOF
python3 "$src/audit.py" "$out"
