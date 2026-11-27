#!/usr/bin/env bash
set -euo pipefail
if ! command -v sage >/dev/null 2>&1; then
  python3 -m pip install 'sympy==1.14.0'
fi
