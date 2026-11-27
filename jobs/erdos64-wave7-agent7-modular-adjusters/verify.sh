#!/usr/bin/env bash
set -euo pipefail

export MATHLIB_DIR="/opt/mathlib4/DownstreamTest"
echo "Using MATHLIB_DIR=$MATHLIB_DIR"
lean --version

mkdir -p out
python3 jobs/erdos64-wave7-agent7-modular-adjusters/audit.py \
  jobs/erdos64-wave7-agent7-modular-adjusters/Wave7Agent7ModularAdjustersAndRewiring.lean \
  out/lean_audit.json
