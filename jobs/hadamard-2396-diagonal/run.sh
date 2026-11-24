#!/usr/bin/env bash
set -euo pipefail
jobdir="$(cd "$(dirname "$0")" && pwd)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
export PYTHONDONTWRITEBYTECODE=1
g++ -std=c++17 -O3 -mpopcnt -Wall -Wextra -Werror "$jobdir/search.cpp" -o "$scratch/search"
mkdir -p "$3"
python3 "$jobdir/shard.py" "$scratch/search" "$1" "$3/result.json"
