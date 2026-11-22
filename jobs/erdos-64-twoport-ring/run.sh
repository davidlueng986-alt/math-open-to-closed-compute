#!/usr/bin/env bash
set -euo pipefail
SHARD="$1"; SHARDS="$2"; OUT="$3"
mkdir -p "$OUT"
: > "$OUT/witnesses.txt"
for n in 20 22 24; do
  nauty-geng -q -c -d3 -D3 "$n" "$SHARD/$SHARDS" |
    jobs/erdos-64-twoport-ring/gadget "$n" > "$OUT/$n.stats" 2>> "$OUT/witnesses.txt"
  cat "$OUT/$n.stats" >&2
done
python3 - "$SHARD" "$SHARDS" "$OUT" <<'PY'
import json,sys
from pathlib import Path
i=int(sys.argv[1]);nshards=int(sys.argv[2]);out=Path(sys.argv[3])
counts={}
for n in (20,22,24):
    f=(out/f"{n}.stats").read_text().split()
    if len(f)!=8 or f[0]!="STATS" or int(f[1])!=n:raise ValueError(f"bad STATS {n}: {f}")
    numbers=list(map(int,f[2:]))
    keys=("base_graphs","after_C4_C8_edge_intersection","after_C16_intersection",
          "connected_twoport_edge_candidates","small_path_ratio_candidates","ring_witnesses")
    counts[str(n)]=dict(zip(keys,numbers))
lines=(out/"witnesses.txt").read_text().splitlines()
if any(not x.startswith("WITNESS ") for x in lines):raise ValueError("verifier crashed or emitted unrecognized stderr")
d={"problem":"ERDOS-64","original_status":"OPEN","shard":i,"shards":nshards,
  "scope":"two-port K=F-e, F cubic order20,22,24; cyclic ring with 2<=t<=128",
  "statistics":counts,"witnesses":lines,"witness_count":len(lines)}
(out/"result.json").write_text(json.dumps(d,indent=2,sort_keys=True)+"\n")
PY
