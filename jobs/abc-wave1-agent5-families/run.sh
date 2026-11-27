#!/usr/bin/env bash
set -euo pipefail
test "$#" -eq 3
test "$1" = 0 && test "$2" = 1
job_dir="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$3"
if command -v sage >/dev/null 2>&1; then
  sage -python "$job_dir/verify.py" "$3"
else
  python3 "$job_dir/verify.py" "$3"
fi
