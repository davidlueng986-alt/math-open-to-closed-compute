#!/usr/bin/env bash
set -euo pipefail
python3 jobs/mols10-relaxed-lns/search.py "$1" "$2" "$3"
