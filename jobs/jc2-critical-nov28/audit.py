#!/usr/bin/env python3
"""Audit compiled declarations and preserve exact source/run identities."""
import hashlib
import json
import pathlib
import re
import sys

out = pathlib.Path(sys.argv[1])
allowed = {"propext", "Classical.choice", "Quot.sound"}

def strip_comments(source):
    result, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            result.append(source[i])
            i += 1
    assert depth == 0
    return "".join(result)

hashes, audits = {}, {}
for path in sorted((out / "source").glob("*.lean")):
    source = strip_comments(path.read_text())
    for token in ("sorry", "admit", "axiom", "native_decide"):
        assert not re.search(r"\b" + token + r"\b", source), (path.name, token)
    hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
    log = (out / (path.stem + ".log")).read_text()
    assert not re.search(r"(?:error|warning):", log), path.name
    audit = {}
    for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
        used = {a.strip() for a in values.split(",") if a.strip()}
        assert used <= allowed, (name, sorted(used))
        audit[name] = sorted(used)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        audit[name] = []
    expected = re.findall(r"^#print axioms\s+(\S+)", source, re.MULTILINE)
    assert expected and len(audit) >= len(expected), (path.name, expected, audit)
    for name in expected:
        assert any(key == name or key.endswith('.' + name) for key in audit), name
    audits[path.name] = audit
assert hashes
result = {
    "status": "PASS",
    "source_commit": (out / "source-commit.txt").read_text().strip(),
    "lean_version": (out / "lean-version.txt").read_text().strip(),
    "mathlib_commit": (out / "mathlib-commit.txt").read_text().strip(),
    "source_sha256": hashes,
    "axioms": audits,
    "scope": "Exact named algebraic declarations only. Analytic geometric applications require the separately written proof; this is not a kernel proof of JC2."
}
(out / "kernel-audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
