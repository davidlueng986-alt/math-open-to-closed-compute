#!/usr/bin/env bash
set -euo pipefail
job=$(cd "$(dirname "$0")" && pwd)
bins=$(mktemp -d)
trap 'rm -rf "$bins"' EXIT
export PYTHONDONTWRITEBYTECODE=1
g++ -O3 -mpopcnt -Wall -Wextra -Werror -std=c++17 "$job/../hadamard-2396-abelian/orbits.cpp" -o "$bins/orbits"
mkdir -p "$3"
python3 "$job/coverage.py" "$bins/orbits" "$1" "$3/result.json"
