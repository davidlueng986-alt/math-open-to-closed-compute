#!/usr/bin/env bash
# usage: run.sh SHARD SHARDS OUTDIR
set -euo pipefail

SHARD="$1"
SHARDS="$2"
OUT="$3"

JOB_DIR="$(cd "$(dirname "$0")" && pwd)"
BIN="$JOB_DIR/search"
if [ ! -x "$BIN" ]; then
  bash "$JOB_DIR/setup.sh"
fi

mkdir -p "$OUT"
export OMP_NUM_THREADS="${OMP_NUM_THREADS:-$(nproc)}"

# Default frontier schedule across (K, M0) pairs above the 2026-10-14 exclusion boundary
# Override with ERDOS203_K and ERDOS203_M0 to focus all shards on a single (K, M0) target.
TARGETS=(
  "71 360"
  "73 360"
  "79 360"
  "83 360"
  "79 720"
  "83 720"
  "89 720"
  "97 720"
)

if [ -n "${ERDOS203_K:-}" ] && [ -n "${ERDOS203_M0:-}" ]; then
  K="$ERDOS203_K"
  M0="$ERDOS203_M0"
else
  IDX=$(( SHARD % ${#TARGETS[@]} ))
  read -r K M0 <<< "${TARGETS[$IDX]}"
fi

LIMIT="${ERDOS203_LIMIT:-50000000}"
RESTARTS="${ERDOS203_RESTARTS:-256}"
SWEEPS="${ERDOS203_SWEEPS:-12}"
KICKS="${ERDOS203_KICKS:-3}"
TIME_LIMIT="${ERDOS203_TIME_LIMIT:-16200}" # 4.5h default (safely under 330m workflow timeout)

"$BIN" \
  --K "$K" \
  --M0 "$M0" \
  --limit "$LIMIT" \
  --restarts "$RESTARTS" \
  --sweeps "$SWEEPS" \
  --kicks "$KICKS" \
  --shard "$SHARD" \
  --shards "$SHARDS" \
  --time-limit "$TIME_LIMIT" \
  --out "$OUT/result.json" \
  --witness "$OUT/witness.txt"
