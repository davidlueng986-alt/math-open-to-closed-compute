#!/usr/bin/env bash
set -euo pipefail
core="$(cd "$(dirname "$0")/../hadamard-2396-399" && pwd)"
bins="$(mktemp -d)"
trap 'rm -rf "$bins"' EXIT
export PYTHONDONTWRITEBYTECODE=1
for exe in search raw phases; do
    g++ -O3 -std=c++17 -mpopcnt -Wall -Wextra -Werror "$core/$exe.cpp" -o "$bins/$exe"
done
mkdir -p "$3"
python3 "$core/refine.py" "$bins" "$1" "$3/result.json"
