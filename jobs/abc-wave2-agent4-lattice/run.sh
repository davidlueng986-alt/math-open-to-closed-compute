#!/usr/bin/env bash
set -euo pipefail
if [ "$1" != 0 ] || [ "$2" != 1 ]; then
  printf 'The exact bounded audit uses one indivisible shard.\n' >&2
  exit 2
fi
job_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
python3 "$job_dir/verify.py" --out "$3"
