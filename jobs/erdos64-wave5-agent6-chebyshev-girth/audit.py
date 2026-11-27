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
    "E64Wave5Agent6." + s for s in (
        "chebMat_double",
        "chebMat_sq_trace_ge",
        "chebMat_sq_trace_sharp",
        "nbMat_rec",
        "chebMat_eq_nbMat_sub",
        "taillessCount_eq_chebMat_trace",
        "taillessCount_double_ge",
        "taillessCount_double_sharp",
        "unconditional_chebyshev_girth_doubling_hasPower",
        "unconditional_chebyshev_girth_doubling_sharp",
        "cubic_girth9_le_131_hasPower",
        "cubic_girth17_le_32771_hasPower",
        "cubic_girth33_le_2147483651_hasPower",
        "four_reg_girth5_le_46_hasPower",
        "erdos64_closed_of_tailless_gt_nonSimple",
    )
}
assert required <= set(audit), sorted(required - set(audit))
res = {
    "status": "PASS",
    "module": module,
    "source_commit": (out / "source-commit.txt").read_text().strip(),
    "lean_version": (out / "lean-version.txt").read_text().strip(),
    "mathlib_commit": (out / "mathlib-commit.txt").read_text().strip(),
    "axioms": audit,
    "source_sha256": source_hashes,
}
(out / "kernel-audit.json").write_text(json.dumps(res, indent=2) + "\n")
print(json.dumps(res, indent=2))
