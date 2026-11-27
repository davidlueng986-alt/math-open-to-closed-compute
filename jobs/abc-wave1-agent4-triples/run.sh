#!/usr/bin/env bash
set -euo pipefail
ABC_AGENT4_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ABC_AGENT4_OUT="${3:?OUTDIR required}"
mkdir -p "$ABC_AGENT4_OUT"
sage -python "$ABC_AGENT4_DIR/search.py" --shard "${1:?SHARD required}" --shards "${2:?SHARDS required}" --out "$ABC_AGENT4_OUT"
python3 "$ABC_AGENT4_DIR/verify_certificates.py" "$ABC_AGENT4_OUT/certificates.json" --output "$ABC_AGENT4_OUT/independent-verification.json"
