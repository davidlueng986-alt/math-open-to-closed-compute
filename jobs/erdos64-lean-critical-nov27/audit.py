#!/usr/bin/env python3
"""Check the actual successful Lean output and all copied proof sources."""
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
assert not re.search(r"(?:error|warning):", text)
audit = {}
for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    used = {a.strip() for a in values.split(",") if a.strip()}
    assert used <= allowed, (name, sorted(used))
    audit[name] = sorted(used)
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    audit[name] = []
assert audit, "No transitive axiom audit was printed"
if module == "AllPairsObstruction":
    required = {"E64AllPairsObstruction." + s for s in
                ("all_pairs_dyadic", "no_four", "no_eight", "no_power", "counterexample")}
    assert required <= set(audit), sorted(required - set(audit))
if module == "MinimalCutCompletion":
    required = {"E64MinimalCut." + s for s in
                ("boundary_singleton_card", "side_minimal_of_nontrivial_minimal",
                 "minimal_side_ports_nonadjacent", "completion_cubic",
                 "cut_into_completion", "minimal_side_completion_three_edge_connected",
                 "minimal_cut_completion", "minimal_nontrivial_cut_completion")}
    assert required <= set(audit), sorted(required - set(audit))
result = {"status": "PASS", "module": module,
          "source_commit": (out / "source-commit.txt").read_text().strip(),
          "lean_version": (out / "lean-version.txt").read_text().strip(),
          "mathlib_commit": (out / "mathlib-commit.txt").read_text().strip(),
          "axioms": audit, "source_sha256": source_hashes,
          "scope": "Only the exact named declarations; no new original or terminal closure follows merely from compilation."}
(out / "kernel-audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
