#!/usr/bin/env bash
set -euo pipefail
SHARD="$1"; SHARDS="$2"; OUTDIR="$3"
mkdir -p "$OUTDIR"
: > "$OUTDIR/witnesses.txt"
for N in 20 22 24; do
  echo "search n=$N shard=$SHARD/$SHARDS" >&2
  nauty-geng -q -c -d3 -D3 "$N" "$SHARD/$SHARDS" |
    jobs/erdos-64-cutvertex/cutvertex "$N" > "$OUTDIR/$N.stats" 2>> "$OUTDIR/witnesses.txt"
  cat "$OUTDIR/$N.stats" >&2
done
python3 - "$SHARD" "$SHARDS" "$OUTDIR" <<'PY'
import json,sys
from pathlib import Path
shard=int(sys.argv[1]);shards=int(sys.argv[2]);out=Path(sys.argv[3])
stats={}
for n in (20,22,24):
    fields=(out/f"{n}.stats").read_text().split()
    if len(fields)!=7 or fields[0]!="STATS" or int(fields[1])!=n:
        raise ValueError(f"malformed stats: {n}: {fields}")
    a=list(map(int,fields[2:]))
    stats[str(n)]=dict(zip(("base_graphs","survive_4_8","survive_4_8_3_7_16",
                             "subdivision_candidates","witnesses"),a))
lines=(out/"witnesses.txt").read_text().splitlines()
if any(not x.startswith("WITNESS ") for x in lines):
    raise ValueError("checker error in witnesses file")
result={"problem":"ERDOS-64","mathematical_status":"OPEN",
        "scope":"edge-subdivision of connected cubic F of order 20,22,24; glue two copies at degree-two vertex",
        "shard":shard,"shards":shards,"statistics":stats,
        "total_witnesses":len(lines),"witnesses":lines}
(out/"result.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
PY
