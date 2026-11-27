#!/usr/bin/env bash
set -euo pipefail
task_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
if command -v sage >/dev/null 2>&1; then
  sage -python "$task_dir/verify.py" "$@"
else
  python3 "$task_dir/verify.py" "$@"
fi
