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
    "E64Wave8Agent2." + s for s in (
        "chebMat_mul_cubic",
        "two_square_cheb_trace_lb",
        "cert_trace_surplus_of_two_square",
        "nonSimpleTaillessCount_le_sum_alpha",
        "hasPower_of_cert",
        "cubic_girth6_le_14_hasPower",
        "cubic_girth7_le_33_hasPower",
        "cubic_girth11_le_143_hasPower",
        "cubic_girth12_le_149_hasPower",
        "cubic_girth13_le_215_hasPower",
        "cubic_girth14_le_274_hasPower",
        "cubic_girth15_le_1483_hasPower",
        "cubic_girth8_le_131_hasPower",
        "cubic_girth9_to_14_above_moore_hasPower",
    )
}
assert required <= set(audit), sorted(required - set(audit))
res = {
    "status": "PASS",
    "module": module,
    "theorem_count": len(audit),
    "source_commit": (out / "source-commit.txt").read_text().strip(),
    "lean_version": (out / "lean-version.txt").read_text().strip(),
    "mathlib_commit": (out / "mathlib-commit.txt").read_text().strip(),
    "axioms": audit,
    "source_sha256": source_hashes,
}
(out / "kernel-audit.json").write_text(json.dumps(res, indent=2) + "\n")
print(json.dumps(res, indent=2))
