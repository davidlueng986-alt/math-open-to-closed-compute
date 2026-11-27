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
assert not re.search(r"(?:error|warning):", text), text
audit = {}
for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    used = {a.strip() for a in values.split(",") if a.strip()}
    assert used <= allowed, (name, sorted(used))
    audit[name] = sorted(used)
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    audit[name] = []
assert audit, "No transitive axiom audit was printed"

required = {"E64Wave4Agent5EG2." + s for s in (
    "near2_of_min_deg_three",
    "eg2_implies_erdos64",
    "near2_of_minimal_bad",
    "eg2_closes_all_leaves",
    "minimal_bad2_exists",
    "minimal_bad2_not_all_ge_three",
    "minimal_bad2_not_one_defect",
    "minimal_bad2_exact_two_defects",
    "minimal_bad2_defects_nonadjacent",
    "eg2_iff_eg_rob",
    "eg_rob_implies_erdos64",
    "eg_rob_closes_all_leaves",
    "minimal_bad2_defect_neighbors_cubic",
    "minimal_bad2_high_independent",
    "minimal_bad2_nonbipartite",
    "minimal_bad2_no_defect_free_two_cut",
)}
assert required <= set(audit), sorted(required - set(audit))

result = {
    "status": "PASS",
    "module": module,
    "audited_count": len(audit),
    "source_commit": (out / "source-commit.txt").read_text().strip(),
    "lean_version": (out / "lean-version.txt").read_text().strip(),
    "mathlib_commit": (out / "mathlib-commit.txt").read_text().strip(),
    "axioms": audit,
    "source_sha256": source_hashes,
    "scope": "Wave 4 Agent #5: EG2 <-> EGRob whole-problem equivalence and MinimalBad2 core collapse (16 audited theorems; original conjecture remains OPEN until EG2-CORE is closed or refuted)."
}
(out / "kernel-audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
