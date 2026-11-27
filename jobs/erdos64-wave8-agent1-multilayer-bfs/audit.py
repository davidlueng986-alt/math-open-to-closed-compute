#!/usr/bin/env python3
import hashlib, json, pathlib, re, sys

out = pathlib.Path(sys.argv[1])
module = sys.argv[2]
allowed = {"propext", "Classical.choice", "Quot.sound"}

def strip_comments(source):
    result, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1; i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            result.append(source[i]); i += 1
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
    "E64Wave8Agent1." + s for s in (
        "cubic_bfs_interior_full_degree",
        "cubic_bfs_top_layer_deg_le_two",
        "cubic_bfs_bottom_expanding_deg_le_two",
        "cubic_two_layer_expanding_max_deg_le_two",
        "cubic_three_layer_bipartite_chorded_forces_sink",
        "cubic_three_layer_expanding_no_bipartite_chorded_cycle",
        "cubic_bfs_shell_degree_cut_identity",
        "multilayer_asymmetric_bfs_lca_cycle_interval",
        "hasPower_of_multilayer_asymmetric_bfs_chorded_cycle",
        "chorded_even_cycle_girth_lower_bound",
        "hasPower_of_girth_bounded_height_chorded_cycle",
        "HetAdjusterChain.realize_length",
        "HetAdjusterChain.realize_isCycle",
        "HetAdjusterChain.brown_completeness",
        "HetAdjusterChain.exists_cycle_of_even_brown_complete",
        "HetAdjusterChain.hasPower_of_even_brown_complete",
        "HetAdjusterChain.hasPower_of_subset_sum_hit",
        "parity_flip_even_cycle_interval_of_odd_cycle",
    )
}
assert required <= set(audit), sorted(required - set(audit))
res = {
    "status": "PASS",
    "module": module,
    "verified_theorem_count": len(required),
    "source_commit": (out / "source-commit.txt").read_text().strip(),
    "lean_version": (out / "lean-version.txt").read_text().strip(),
    "mathlib_commit": (out / "mathlib-commit.txt").read_text().strip(),
    "axioms": audit,
    "source_sha256": source_hashes,
}
(out / "kernel-audit.json").write_text(json.dumps(res, indent=2) + "\n")
print(json.dumps(res, indent=2))
