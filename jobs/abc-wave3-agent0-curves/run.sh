#!/usr/bin/env bash
set -euo pipefail
test "$1" = 0
test "$2" = 1
job_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p "$3"
sage -python "$job_dir/verify.py" "$3"
