#!/usr/bin/env python3
"""Strict kernel and transitive-axiom audit for Wave 5 Agent #4 Whole-Problem Closure."""
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
    "E64Wave5Agent4." + s for s in (
        "nonBacktracking_lt_girth_add_two_isCyclicallyNonBacktracking",
        "nonBacktracking_lt_girth_add_two_isCycle",
        "no_nonBacktracking_closed_pow2_lt_girth_add_two",
        "tailless_pow2_lt_three_girth_not_square",
        "nonSimple_tailless_exists_split_ge_girth",
        "nonSimple_tailless_mersenne_girth_split_lengths",
        "hasPower_of_second_window_no_split",
        "erdos64_of_two_window_nonBacktracking",
        "no_pow2_cycle_in_twoFactor",
        "mcontract_general_switching_lift",
        "mcontract_cycle_length_plus_switches_not_pow2",
        "mcontract_pow2_cycle_strictly_mixed",
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
