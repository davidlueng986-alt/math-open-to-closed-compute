#!/usr/bin/env bash
set -euo pipefail
SHARD="$1"; SHARDS="$2"; OUTDIR="$3"
mkdir -p "$OUTDIR"
g++ -O3 -std=c++17 jobs/mols10-coarse-lift/coarse.cpp -o /tmp/mols10_coarse
/tmp/mols10_coarse exact "$SHARD" "$SHARDS" > "$OUTDIR/exact.txt" 2> "$OUTDIR/exact.log"
/tmp/mols10_coarse 120 "$((20261124+SHARD))" > "$OUTDIR/heuristic.txt" 2> "$OUTDIR/heuristic.log"
python3 jobs/mols10-coarse-lift/summarize.py "$SHARD" "$SHARDS" "$OUTDIR"
