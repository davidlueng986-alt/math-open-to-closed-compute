#!/usr/bin/env bash
set -euo pipefail
sudo apt-get update -qq
sudo apt-get install -y -qq git cmake ninja-build build-essential pkg-config \
  libboost-all-dev libgmp-dev zlib1g-dev libtbb-dev
git clone --recursive https://github.com/markirch/sat-modulo-symmetries.git sms
git -C sms checkout 464f12f
git -C sms submodule update --init --recursive
git clone https://github.com/ciaranm/glasgow-subgraph-solver sms/glasgow-subgraph-solver
git -C sms/glasgow-subgraph-solver checkout 1217f5b
(cd sms && bash ./build-and-install.sh -s -l)
test -x "$HOME/.local/bin/smsg"
"$HOME/.local/bin/smsg" --help > /dev/null
python3 -c 'from pysms.graph_builder import GraphEncodingBuilder; print("PySMS loaded")'
