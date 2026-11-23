#!/usr/bin/env bash
set -euo pipefail
if [ "${MATH_COMPUTE_SMS_REV:-}" = "464f12f" ] && command -v smsg >/dev/null 2>&1 && python3 -c 'from pysms.graph_builder import GraphEncodingBuilder' >/dev/null 2>&1; then
  echo 'Using preinstalled SMS and PySMS.'
  exit 0
fi
sudo apt-get update -qq
sudo apt-get install -y -qq git cmake ninja-build build-essential pkg-config \
  libboost-all-dev libgmp-dev zlib1g-dev libtbb-dev
git clone --recursive https://github.com/markirch/sat-modulo-symmetries.git sms
git -C sms checkout 464f12f
git -C sms submodule update --init --recursive
git clone https://github.com/ciaranm/glasgow-subgraph-solver sms/glasgow-subgraph-solver
git -C sms/glasgow-subgraph-solver checkout 1217f5b
# The pinned SMS CMake links the static Glasgow archive without its GMP dependency.
# Insert GMP *after* the archive in the inherited CMake link list (not LDFLAGS).
python3 - <<'PY'
from pathlib import Path
p=Path("sms/CMakeLists.txt")
s=p.read_text()
anchor='link_libraries("${PROJECT_SOURCE_DIR}/glasgow-subgraph-solver/build/gss/libglasgow_subgraphs.a")'
assert s.count(anchor)==1, "unexpected pinned CMake source"
s=s.replace(anchor,anchor+'\n\tfind_library(GMP_LIBRARY NAMES gmp REQUIRED)\n\tlink_libraries(${GMP_LIBRARY})')
p.write_text(s)
PY
(cd sms && bash ./build-and-install.sh -s -l)
test -x "$HOME/.local/bin/smsg"
ldd "$HOME/.local/bin/smsg"
# --help may return nonzero in this version; the actual SAT positive control is decisive.
"$HOME/.local/bin/smsg" --help > /dev/null || true
python3 -c 'from pysms.graph_builder import GraphEncodingBuilder; print("PySMS loaded")'
