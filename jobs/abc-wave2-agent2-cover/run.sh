#!/usr/bin/env bash
set -euo pipefail
SHARD_INDEX="${1:-0}"
SHARD_COUNT="${2:-1}"
OUT_DIR="${3:?output directory required}"
if [ "$SHARD_INDEX" != "0" ] || [ "$SHARD_COUNT" != "1" ]; then
  echo "This deterministic complete finite verifier accepts one shard only." >&2
  exit 2
fi
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p "$OUT_DIR"
python3 "$SCRIPT_DIR/verify.py" --bound 600 --out "$OUT_DIR"
