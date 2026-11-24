#!/usr/bin/env bash
set -euo pipefail
jobdir="$(cd "$(dirname "$0")" && pwd)"
bins="$(mktemp -d)"
trap 'rm -rf "$bins"' EXIT
export PYTHONDONTWRITEBYTECODE=1
for exe in search phases raw; do
    g++ -O3 -std=c++17 -mpopcnt -Wall -Wextra -Werror "$jobdir/$exe.cpp" -o "$bins/$exe"
done
mkdir -p "$3"
python3 "$jobdir/shard.py" "$bins" "$1" "$3/result.json"
