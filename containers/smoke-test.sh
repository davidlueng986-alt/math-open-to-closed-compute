#!/usr/bin/env bash
set -euo pipefail
toolbox="$1"
image="$2"
case "$toolbox" in
  sat)
    docker run --rm --entrypoint bash "$image" -c 'set -eu; command -v smsg; command -v nauty-geng; command -v z3; command -v minisat; python3 -c "from pysms.graph_builder import GraphEncodingBuilder; import pysat,networkx,numpy"'
    docker run --rm --entrypoint python3 "$image" /opt/math-toolbox/test-math-tools.py
    ;;
  sage)
    docker run --rm --entrypoint bash "$image" -c 'set -eu; sage -c "assert factor(360).value() == 360 and len(factor(360)) == 3"; command -v nauty-geng; command -v z3; command -v minisat'
    ;;
  lean)
    docker run --rm --entrypoint bash "$image" -c 'set -eu; lean --version; cd /opt/mathlib4; printf "import Mathlib\n#check Nat.add_comm\n" > /tmp/smoke.lean; lake env lean /tmp/smoke.lean'
    ;;
  *) echo "Unknown toolbox: $toolbox" >&2; exit 1 ;;
esac
