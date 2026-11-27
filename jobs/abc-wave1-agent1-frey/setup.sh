#!/usr/bin/env bash
set -euo pipefail
if command -v sage >/dev/null 2>&1; then
  sage -python -c 'import sympy'
else
  python3 -m pip install --user 'sympy==1.14.0'
fi
