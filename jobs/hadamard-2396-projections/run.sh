#!/usr/bin/env bash
set -euo pipefail
jobdir="$(cd "$(dirname "$0")" && pwd)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$3"
export PYTHONDONTWRITEBYTECODE=1
g++ -std=c++17 -O3 -Wall -Wextra -Werror "$jobdir/search399.cpp" -o "$scratch/search399"
total=$(python3 "$jobdir/shapes.py")
for ((i=$1; i<total; i+=$2)); do
  python3 "$jobdir/shapes.py" "$i" | "$scratch/search399" > "$scratch/shape-$i.json"
done
python3 "$jobdir/lift.py" "$1" 45 5 "$scratch/lift.json"
python3 - "$scratch" "$3" "$1" "$2" <<'PY'
import json, sys
from pathlib import Path
src, out = map(Path,sys.argv[1:3])
shapes={f.stem.split("-")[1]:json.loads(f.read_text()) for f in src.glob("shape-*.json")}
result={"shard":int(sys.argv[3]),"shards":int(sys.argv[4]),"shapes":shapes,
        "lift":json.loads((src/"lift.json").read_text())}
(out/"result.json").write_text(json.dumps(result)+"\n")
PY
