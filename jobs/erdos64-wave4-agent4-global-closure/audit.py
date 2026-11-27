#!/usr/bin/env python3
import json, pathlib, re, sys

out_dir = pathlib.Path(sys.argv[1])
module = sys.argv[2]
log_text = (out_dir / f"{module}.log").read_text()

allowed = {"propext", "Classical.choice", "Quot.sound"}
required = [
    "E64Wave4Agent4.contractSet_card_lt",
    "E64Wave4Agent4.contractSet_degree_some",
    "E64Wave4Agent4.contractSet_near",
    "E64Wave4Agent4.minimal_bad_contractSet_dyadic_ear",
    "E64Wave4Agent4.minimal_bad_two_packing_dyadic_path",
    "E64Wave4Agent4.minimal_bad_no_synchronized_contraction",
    "E64Wave4Agent4.erdos64_closed_of_global_target",
]

axioms = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log_text):
    thm = m.group(1)
    ax = [x.strip() for x in m.group(2).split(",") if x.strip()]
    axioms[thm] = ax
for m in re.finditer(r"'([^']+)' does not depend on any axioms", log_text):
    axioms[m.group(1)] = []

errors = []
for r in required:
    if r not in axioms:
        errors.append(f"Missing axiom report for {r}")
    else:
        bad = set(axioms[r]) - allowed
        if bad:
            errors.append(f"{r} uses disallowed axioms: {sorted(bad)}")

src_text = (out_dir / "source" / f"{module}.lean").read_text()
for banned in ["sorry", "admit", "axiom ", "native_decide"]:
    if re.search(rf"\b{banned.strip()}\b", src_text):
        errors.append(f"Banned token '{banned.strip()}' found in {module}.lean")

report = {
    "module": module,
    "required_theorems": required,
    "axioms": axioms,
    "errors": errors,
    "status": "PASS" if not errors else "FAIL",
}
(out_dir / "kernel-audit.json").write_text(json.dumps(report, indent=2))
print(json.dumps(report, indent=2))
if errors:
    sys.exit(1)
