#!/usr/bin/env bash
set -euo pipefail
python3 jobs/erdos-64-s3-bicon/search.py "$1" "$2" "$3"
