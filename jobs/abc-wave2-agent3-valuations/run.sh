#!/usr/bin/env bash
set -euo pipefail
task_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
task_shard="${1:-0}"
task_shards="${2:-1}"
task_out="${3:?output directory required}"
mkdir -p -- "$task_out"
python3 "$task_dir/verify.py" --shard "$task_shard" --shards "$task_shards" --out "$task_out"
