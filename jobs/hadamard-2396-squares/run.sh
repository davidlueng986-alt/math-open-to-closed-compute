#!/usr/bin/env bash
set -euo pipefail
job=$(cd "$(dirname "$0")" && pwd)
bins=$(mktemp -d)
trap 'rm -rf "$bins"' EXIT
export PYTHONDONTWRITEBYTECODE=1
for program in "$job/search.cpp:squares" "$job/../hadamard-2396-abelian/orbits.cpp:orbits"; do
    g++ -O3 -mpopcnt -Wall -Wextra -Werror -std=c++17 "${program%:*}" -o "$bins/${program##*:}"
done
mkdir -p "$3"
python3 "$job/scan.py" "$bins" "$job/templates.txt" "$1" "$2" "$3/result.json"
