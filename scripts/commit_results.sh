#!/usr/bin/env bash
# Commit summary/ to runs/<job>/<run id>/ on the "results" branch (created on first use).
# Uses the workflow's own GITHUB_TOKEN; pushes made with it do not start other workflows.
set -euo pipefail

dest="runs/${JOB}/${GITHUB_RUN_ID}"
work="$(mktemp -d)"
git init -q "$work"
cd "$work"
git config user.name "github-actions[bot]"
git config user.email "41898282+github-actions[bot]@users.noreply.github.com"
git remote add origin "https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git"

if git fetch -q --depth 1 origin results 2>/dev/null; then
  git checkout -q -b results FETCH_HEAD
else
  git checkout -q --orphan results
  printf '# Results\n\nOne folder per run: runs/<job>/<run id>/summary.json. Written by the sharded-run workflow.\n' > README.md
fi

mkdir -p "$dest"
cp -R "$GITHUB_WORKSPACE/summary/." "$dest/"
git add -A
git commit -q -m "results: ${JOB} run ${GITHUB_RUN_ID}"

for attempt in 1 2 3 4 5; do
  if git push -q origin HEAD:results; then
    echo "committed to results:${dest}"
    exit 0
  fi
  echo "push attempt ${attempt} failed; rebasing on the latest results branch"
  sleep $((attempt * 3))
  git fetch -q origin results
  git rebase -q FETCH_HEAD
done
echo "could not push results after 5 attempts; the summary artifact still has them" >&2
exit 1
