#!/usr/bin/env python3
"""Strict kernel and transitive-axiom audit for Wave 5 Agent #5."""
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
    "E64Wave5Agent5." + s for s in (
        "isNonBacktracking_append_iff",
        "isNonBacktracking_reverse",
        "nonBacktracking_tail_peel",
        "tailless_nonBacktracking_lt_three_girth_decomp",
        "no_equal_half_cycles_of_not_hasPower",
        "cubic_no_figure_eight_split",
        "unique_nonBacktracking_walk_of_sum_lt_girth",
        "unique_nonBacktracking_walk_of_half_girth",
        "exists_pow2_in_tripling_window_of_octave_top",
        "hasPower_iff_nonBacktracking_surplus",
        "erdos64_of_nonBacktracking_surplus",
        "transition_walk_lift_length",
        "hasPower_of_transition_pow2_lift",
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
