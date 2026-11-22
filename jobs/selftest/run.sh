#!/usr/bin/env bash
# usage: run.sh SHARD SHARDS OUTDIR
set -euo pipefail
python3 "$(dirname "$0")/count_primes.py" "$1" "$2" "$3"
