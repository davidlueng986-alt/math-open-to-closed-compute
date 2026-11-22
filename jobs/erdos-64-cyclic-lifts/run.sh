#!/usr/bin/env bash
set -euo pipefail
SHARD="$1"
SHARDS="$2"
OUTDIR="$3"
python3 jobs/erdos-64-cyclic-lifts/search.py "$SHARD" "$SHARDS" "$OUTDIR"
