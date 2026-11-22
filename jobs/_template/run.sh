#!/usr/bin/env bash
# Copy this folder to jobs/<your-job>/ and replace the body.
# usage: run.sh SHARD SHARDS OUTDIR   (SHARD counts from 0; SHARDS is the total)
set -euo pipefail
shard="$1"; shards="$2"; out="$3"

# 1. Work out this shard's slice of the problem from (shard, shards), deterministically.
# 2. Stop on your own before GitHub's limit, e.g. wrap a long solver in `timeout 5h ...`,
#    and write what was finished, so an unfinished shard can be split further and rerun.
# 3. Write out/result.json (required) and any small extra files to $out.

printf '{"shard": %s, "shards": %s, "status": "template"}\n' "$shard" "$shards" > "$out/result.json"
