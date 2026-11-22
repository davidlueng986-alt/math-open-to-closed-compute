#!/usr/bin/env python3
"""Merge shard outputs into summary/.

    python3 scripts/collect.py           write summary/summary.json, then run jobs/<job>/merge.py if present
    python3 scripts/collect.py --check   exit 1 if summary.json reports missing shards or a failed merge

Shard i's files arrive in shards/shard-<i>/ (one artifact per shard). Every shard must write result.json.
"""
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SHARDS_DIR = Path("shards")
SUMMARY_DIR = Path("summary")
SUMMARY = SUMMARY_DIR / "summary.json"
INLINE_LIMIT = 200_000  # bytes of shard results copied into summary.json


def read_json(path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


def collect():
    job = os.environ["JOB"]
    expected = int(float(os.environ["SHARDS"]))
    SUMMARY_DIR.mkdir(exist_ok=True)

    results, timing, missing = {}, {}, []
    for i in range(expected):
        folder = SHARDS_DIR / f"shard-{i}"
        result = read_json(folder / "result.json")
        if result is None:
            missing.append(i)
        else:
            results[str(i)] = result
        seconds = read_json(folder / "_timing.json")
        if seconds is not None:
            timing[str(i)] = seconds.get("seconds")

    server = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    run_id = os.environ.get("GITHUB_RUN_ID", "local")
    summary = {
        "job": job,
        "run_id": run_id,
        "run_url": f"{server}/{repo}/actions/runs/{run_id}" if repo else None,
        "commit": os.environ.get("GITHUB_SHA"),
        "shards_expected": expected,
        "shards_with_result": len(results),
        "missing_shards": missing,
        "seconds_per_shard": timing,
        "complete": not missing,
    }
    if len(json.dumps(results)) <= INLINE_LIMIT:
        summary["results"] = results
    else:
        summary["results"] = "too large to inline; see the shard artifacts"

    merge = ROOT / "jobs" / job / "merge.py"
    if merge.is_file():
        proc = subprocess.run([sys.executable, str(merge), str(SHARDS_DIR), str(SUMMARY_DIR)],
                              capture_output=True, text=True)
        summary["merge"] = {"exit_code": proc.returncode, "output": (proc.stdout + proc.stderr)[-4000:]}
        print(proc.stdout, end="")
        print(proc.stderr, end="", file=sys.stderr)

    SUMMARY.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"{job}: {len(results)}/{expected} shards with results; missing: {missing or 'none'}")


def check():
    summary = read_json(SUMMARY)
    if summary is None:
        sys.exit("summary/summary.json is missing")
    problems = []
    if not summary.get("complete"):
        problems.append(f"missing shards {summary.get('missing_shards')}")
    if summary.get("merge", {}).get("exit_code", 0) != 0:
        problems.append("merge.py failed")
    if problems:
        sys.exit("; ".join(problems))
    print("all shards present; merge OK")


if __name__ == "__main__":
    check() if "--check" in sys.argv[1:] else collect()
