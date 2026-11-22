#!/usr/bin/env bash
set -euo pipefail
export LD_LIBRARY_PATH="$HOME/.local/lib:${LD_LIBRARY_PATH:-}"
python3 jobs/erdos-64-sms-direct/run.py "$1" "$2" "$3"
