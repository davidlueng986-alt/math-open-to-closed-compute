#!/usr/bin/env bash
set -euo pipefail
if [ "$1" != 0 ] || [ "$2" != 1 ]; then
  printf 'This kernel audit is one indivisible shard.\n' >&2
  exit 2
fi
job_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p "$3"
out_dir="$(cd -- "$3" && pwd)"
cd /opt/mathlib4
lean --version | tee "$out_dir/lean-version.txt"
grep -F 'version 4.36.0' "$out_dir/lean-version.txt"
git rev-parse HEAD > "$out_dir/mathlib-commit.txt"
lake env lean -o "$out_dir/Structural.olean" "$job_dir/Structural.lean" 2>&1 | tee "$out_dir/kernel.log"
python3 "$job_dir/audit.py" "$job_dir/Structural.lean" "$out_dir"
