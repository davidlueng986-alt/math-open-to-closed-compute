#!/usr/bin/env python3
"""Audit the actual Lean kernel dependency output for every exported theorem."""
import hashlib
import json
import os
from pathlib import Path
import re
import sys


def main():
    source_path, log_path, output_path = map(Path, sys.argv[1:])
    source = source_path.read_text()
    log = log_path.read_text()
    required = re.findall(r"^#print axioms\s+(\S+)\s*$", source, re.M)
    assert required and len(required) == len(set(required)), "Missing or duplicate theorem audits"
    assert not re.search(r"\bsorryAx\b|\bLean\.ofReduceBool\b", log), "Unproved or native evaluation axiom"
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    dependencies = {}
    for name in required:
        found = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
        if found:
            used = {x.strip() for x in found.group(1).split(",") if x.strip()}
        else:
            assert "'" + name + "' does not depend on any axioms" in log, f"No kernel audit for {name}"
            used = set()
        assert used <= allowed, f"Unexpected axioms for {name}: {used - allowed}"
        dependencies[name] = sorted(used)
    result = {
        "status": "PASS",
        "scope": "Named cap and sumset lemmas only; not a formal proof of a seven-dimensional numerical bound or the exact maximum.",
        "source_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
        "lean": "4.36.0",
        "mathlib": "fc4f59e577feb1a4956671bc04ac18aaaf8cd842",
        "image_digest": "sha256:8ba27c4e6be1aff22d80e6444f3ef7a4d0fc0438bcadf55ef39d2c17c74ae116",
        "commit": os.getenv("GITHUB_SHA"),
        "run_id": os.getenv("GITHUB_RUN_ID"),
        "run_attempt": os.getenv("GITHUB_RUN_ATTEMPT"),
        "theorem_dependencies": dependencies,
    }
    output_path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
