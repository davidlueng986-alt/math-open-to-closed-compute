#!/usr/bin/env bash
set -euo pipefail
sudo apt-get update -qq
sudo apt-get install -y -qq nauty
g++ -O3 -std=c++17 -Wall -Wextra -o jobs/erdos-64-twoport-ring/gadget jobs/erdos-64-twoport-ring/gadget.cpp
