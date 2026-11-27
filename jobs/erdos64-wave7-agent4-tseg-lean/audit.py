#!/usr/bin/env python3
"""Strict kernel and transitive-axiom audit for Wave 7 Agent #4 TS-EG formalization."""
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
    "E64Wave7Agent4." + s for s in (
        "c8_mchord_forces_two_c5",
        "c5_matching_free_c8_mchordless",
        "girth_boundary_chord_forces_exact_half",
        "tseg_girth_boundary_mchord_forces_two_odd",
        "bipartite_girth_pow2_shatter",
        "bipartite_c16_mchord_forces_c6_c12",
        "bipartite_c4_c6_c8_free_c16_mchordless",
        "flipSide_preserves_transitionSystem",
        "blowUp_gauge_iso",
        "gauge_preserves_internalSwitches",
        "gauge_preserves_totalSwitches",
        "gauge_balanced_even_switches",
        "gauge_balanced_odd_cycle_avoids_pow2",
        "bipartite_gauge_balanced_blowUp_bipartite",
        "balanced_blowUp_closed_walk_even_matching",
        "triangle_free_balanced_no_c5_matching",
        "triangle_free_balanced_c8_mchordless",
        "balanced_2factor_chord_forces_tseg",
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
