#!/usr/bin/env bash
set -euo pipefail
TASK_OUT="${3:-/tmp/abc-wave3-agent3}"
mkdir -p "$TASK_OUT"
sage -python "$(dirname "$0")/verify.py" --require-sage --output "$TASK_OUT"
