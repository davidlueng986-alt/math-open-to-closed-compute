#!/usr/bin/env bash
set -euo pipefail

JOB_DIR="$(cd "$(dirname "$0")" && pwd)"
echo "[setup] compiler: $(g++ --version | head -n 1)"
g++ -O3 -march=native -fopenmp -std=c++17 "$JOB_DIR/search.cpp" -o "$JOB_DIR/search"
test -x "$JOB_DIR/search"
echo "[setup] built $JOB_DIR/search successfully"
