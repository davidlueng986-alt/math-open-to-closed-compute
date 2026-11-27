import json, re, sys

log_path, out_path = sys.argv[1], sys.argv[2]
text = open(log_path).read()
allowed = {"propext", "Classical.choice", "Quot.sound"}
expected = [
    "E64Wave4Agent2.minimal_bad_two_packing_dyadic_path",
    "E64Wave4Agent2.near_quotient",
    "E64Wave4Agent2.card_qvert_lt",
]
found = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
    name = m.group(1)
    axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
    found[name] = axs

errors = []
for name in expected:
    if name not in found:
        errors.append(f"Missing axiom print for {name}")
    else:
        bad = [a for a in found[name] if a not in allowed]
        if bad:
            errors.append(f"Disallowed axioms for {name}: {bad}")

report = {"expected": expected, "axioms": found, "allowed": sorted(allowed), "errors": errors}
open(out_path, "w").write(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
if errors:
    sys.exit(1)
