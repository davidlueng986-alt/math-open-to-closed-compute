#!/usr/bin/env python3
"""Strict kernel and transitive-axiom audit for Wave 8 Agent #4 Girth 9-14 formalization."""
import hashlib
import json
import pathlib
import re
import sys

out = pathlib.Path(sys.argv[1])
module = sys.argv[2]
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

source_hashes = {}
for path in sorted((out / "source").glob("*.lean")):
    src = strip_comments(path.read_text())
    for tok in ("sorry", "admit", "axiom", "native_decide"):
        assert not re.search(r"\b" + tok + r"\b", src), (path.name, tok)
    source_hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()

text = (out / f"{module}.log").read_text()
assert not re.search(r"(?:error|warning):", text), text
audit = {}
for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    used = {a.strip() for a in values.split(",") if a.strip()}
    assert used <= allowed, (name, sorted(used))
    audit[name] = sorted(used)
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    audit[name] = []

required = {
    "E64Wave8Agent4." + s for s in (
        "locallyNB_closed_three_le_length",
        "locallyNB_closed_contains_cycle",
        "locallyNB_closed_ge_girth",
        "closedNB_lt_two_girth_isCycle",
        "girth9_closedNB16_is_pow2_cycle",
        "girth_gt_half_pow2_closedNB_is_pow2_cycle",
        "nbPoly_perron",
        "nbPoly_even_neg",
        "nbPoly_add",
        "nbPoly_doubling",
        "nbPoly_even_lower_bound",
        "cubic_nb16_unconditional_floor",
        "cubic_nb16_trace_pos_nonbipartite",
        "cubic_nb16_trace_pos_bipartite",
        "dreg_nb_even_trace_pos",
        "girth_no_two_disjoint_short_paths",
        "girth9_disjoint_len8_paths_has_power",
    )
}
assert required <= set(audit), sorted(required - set(audit))
res = {
    "status": "PASS",
    "module": module,
    "audited_theorems": len(required),
    "source_commit": (out / "source-commit.txt").read_text().strip(),
    "lean_version": (out / "lean-version.txt").read_text().strip(),
    "mathlib_commit": (out / "mathlib-commit.txt").read_text().strip(),
    "axioms": audit,
    "source_sha256": source_hashes,
}
(out / "kernel-audit.json").write_text(json.dumps(res, indent=2) + "\n")
print(json.dumps(res, indent=2))
