#!/usr/bin/env bash
set -euo pipefail
sudo apt-get update -qq
sudo apt-get install -y -qq nauty
python3 -m pip install --disable-pip-version-check 'numpy>=1.26,<3' 'networkx>=3,<4'
python3 jobs/erdos-64-contracted3-20/selftest.py
g++ -O3 -std=c++17 -Wall -Wextra -o jobs/erdos-64-contracted3-20/cover_check jobs/erdos-64-cyclic-lifts/cover_check.cpp
