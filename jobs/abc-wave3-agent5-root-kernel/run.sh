#!/usr/bin/env bash
set -euo pipefail
task_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
task_shard="${1:-0}"
task_shards="${2:-1}"
task_out="${3:?output directory required}"
if [[ "$task_shard" != "0" || "$task_shards" != "1" ]]; then
  echo "This exact verifier uses one shard." >&2
  exit 2
fi
mkdir -p -- "$task_out"
python3 "$task_dir/verify.py" --out "$task_out"
