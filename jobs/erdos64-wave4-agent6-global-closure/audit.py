#!/usr/bin/env python3
"""Strict kernel and transitive-axiom audit for Wave 4 Agent #6 Global Closure."""
import hashlib
import json
import pathlib
import re
import sys

out = pathlib.Path(sys.argv[1])
module = sys.argv[2]
allowed = {"propext", "Classical.choice", "Quot.sound"}
source_hashes = {}

def strip_comments(source):
    result = []
    depth = 0
    i = 0
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

for path in sorted((out / "source").glob("*.lean")):
    source = strip_comments(path.read_text())
    for token in ("sorry", "admit", "axiom", "native_decide"):
        assert not re.search(r"\b" + token + r"\b", source), (path.name, token)
    source_hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()

text = (out / (module + ".log")).read_text()
assert not re.search(r"(?:error|warning):", text), "Compiler error or warning detected"
audit = {}
for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    used = {a.strip() for a in values.split(",") if a.strip()}
    assert used <= allowed, (name, sorted(used))
    audit[name] = sorted(used)
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    audit[name] = []

required = {
    "E64Wave4Agent6." + s for s in (
        "minimal_bad_not_bip",
        "bipDeg_add_frustDeg",
        "exists_max_cut",
        "max_cut_frustDeg_le_bipDeg",
        "minimal_bad_max_cut_frustrated_matching",
        "original_of_max_cut_bipartite_power",
        "select_wfree_minimal_two_cut",
        "wfree_minimal_side_ports_nonadjacent",
        "completion_min_deg_three",
        "completion_sdiff_edge",
        "wfree_minimal_bad_two_cut_normal_form",
        "no_minimal_bad_small_cut_two_of_edge_avoiding",
        "exclude_cn_core_of_edge_avoiding",
        "original_of_edge_avoiding_and_low3",
        "matching_contraction_simple_4reg_power",
    )
}
assert required <= set(audit), sorted(required - set(audit))
result = {
    "status": "PASS",
    "module": module,
    "audited_theorems": len(required),
    "source_commit": (out / "source-commit.txt").read_text().strip(),
    "lean_version": (out / "lean-version.txt").read_text().strip(),
    "mathlib_commit": (out / "mathlib-commit.txt").read_text().strip(),
    "axioms": audit,
    "source_sha256": source_hashes,
}
(out / "kernel-audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
