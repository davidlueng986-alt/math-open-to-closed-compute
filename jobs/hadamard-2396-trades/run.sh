#!/usr/bin/env bash
set -euo pipefail
jobdir="$(cd "$(dirname "$0")" && pwd)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
export PYTHONDONTWRITEBYTECODE=1
g++ -std=c++17 -O3 -Wall -Wextra -Werror "$jobdir/../hadamard-2396-projections/trades.cpp" -o "$scratch/trades"
mkdir -p "$3"
python3 "$jobdir/search.py" "$scratch/trades" "$1" "$2" "$3/result.json"
