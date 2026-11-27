#!/usr/bin/env bash
set -euo pipefail
task_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
task_shard="${1:-0}"
task_shards="${2:-1}"
task_out="${3:?output directory required}"
if [[ "$task_shard" != "0" || "$task_shards" != "1" ]]; then
  echo "This independent frozen-snapshot audit uses one shard." >&2
  exit 2
fi
mkdir -p -- "$task_out"
python3 "$task_dir/audit.py" --root "$task_dir/snapshot" --output "$task_out/result.json"
cp "$task_dir/snapshot/research/ABC/wave3_agent6/snapshot-lock.json" "$task_out/snapshot-lock.json"

