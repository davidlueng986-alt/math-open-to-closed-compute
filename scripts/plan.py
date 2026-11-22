#!/usr/bin/env python3
"""Validate the workflow inputs and print the shard matrix for $GITHUB_OUTPUT."""
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
JOB_NAME = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]*$")


def integer(name, low, high):
    raw = os.environ.get(name, "")
    try:
        value = int(float(raw))
    except ValueError:
        sys.exit(f"{name} must be a whole number, got {raw!r}")
    if not low <= value <= high:
        sys.exit(f"{name} must be between {low} and {high}, got {value}")
    return value


def main():
    job = os.environ.get("JOB", "")
    if not JOB_NAME.match(job) or ".." in job:
        sys.exit(f"JOB must be a folder name under jobs/ (letters, digits, '-', '_', '.'), got {job!r}")
    if not (ROOT / "jobs" / job / "run.sh").is_file():
        sys.exit(f"jobs/{job}/run.sh not found")
    shards = integer("SHARDS", 1, 256)
    integer("TIMEOUT_MINUTES", 1, 360)
    integer("MAX_PARALLEL", 1, 256)
    print("matrix=" + json.dumps(list(range(shards))))


if __name__ == "__main__":
    main()
