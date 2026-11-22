#!/usr/bin/env bash
set -euo pipefail
if ! printf '#include <gmp.h>\n' | g++ -x c++ -E - >/dev/null 2>&1; then
  sudo apt-get update -q
  sudo apt-get install -y libgmp-dev
fi
