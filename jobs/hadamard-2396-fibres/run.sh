#!/usr/bin/env bash
set -euo pipefail
exec python3 "$(dirname "$0")/search.py" "$1" "$2" "$3"
