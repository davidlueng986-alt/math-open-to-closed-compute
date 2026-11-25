#!/usr/bin/env bash
set -euo pipefail
file="$1"
case "$file" in assignment.json|result.json|proof.lean) ;; *) exit 2;; esac
path="results/runs/pequalnp/$GITHUB_RUN_ID/$file"
body="$(python3 -c 'import base64,json,sys; print(json.dumps({"message":"P vs NP attempt evidence","branch":"results","content":base64.b64encode(open(sys.argv[1],"rb").read()).decode()}))' "$RUNNER_TEMP/pnp-public/$file")"
# One append-only path per run, no modification of existing research results.
printf '%s' "$body" | gh api --method PUT "repos/$GITHUB_REPOSITORY/contents/$path" --input - --silent
