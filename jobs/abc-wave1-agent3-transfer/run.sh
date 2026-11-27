#!/usr/bin/env bash
set -euo pipefail
job_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
python3 "$job_dir/verify.py" --shard "$1" --shards "$2" --outdir "$3"
