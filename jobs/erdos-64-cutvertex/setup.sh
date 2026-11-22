#!/usr/bin/env bash
set -euo pipefail
sudo apt-get update -qq
sudo apt-get install -y -qq nauty
g++ -O3 -std=c++17 -Wall -Wextra -o jobs/erdos-64-cutvertex/cutvertex jobs/erdos-64-cutvertex/cutvertex.cpp
