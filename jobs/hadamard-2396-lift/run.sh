#!/usr/bin/env bash
set -euo pipefail
exec python3 "$(dirname "$0")/search_lift.py" "$1" "$2" "$3"
