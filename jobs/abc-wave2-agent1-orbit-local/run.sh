#!/usr/bin/env bash
set -euo pipefail
shard="${1:-0}"
shards="${2:-1}"
out="${3:?output directory required}"
if [[ "$shard" != 0 || "$shards" != 1 ]]; then
  echo 'This exact bounded audit is unsharded.' >&2
  exit 2
fi
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p "$out"
python3 "$here/verify.py" --out "$out"
