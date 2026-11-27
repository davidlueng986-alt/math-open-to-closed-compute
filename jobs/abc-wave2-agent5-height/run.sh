#!/usr/bin/env bash
set -euo pipefail
task_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
if command -v sage >/dev/null 2>&1; then
  sage -python "$task_dir/verify.py" "$@" --require-sage
elif [ "${GITHUB_ACTIONS:-false}" = true ]; then
  printf 'Sage is required for the hosted Agent5 geometric audit.\n' >&2
  exit 2
else
  python3 "$task_dir/verify.py" "$@"
fi
