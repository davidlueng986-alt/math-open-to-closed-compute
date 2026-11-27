import json, pathlib, re, sys

out = pathlib.Path(sys.argv[1])
log = (out / "Wave4Agent3GlobalClosure.log").read_text()
expected = [
    "E64Wave4Agent3.partition_has_pow2_iff_one_two_four",
    "E64Wave4Agent3.GraphCover.covering_lift_power_cycle_of_degree_two_or_four",
    "E64Wave4Agent3.minimal_bad_no_two_or_four_cover",
    "E64Wave4Agent3.erdos64_of_global_two_or_four_cover",
    "E64Wave4Agent3.minimal_bad_two_indep_avoiding_dyadic_path",
]
allowed = {"propext", "Classical.choice", "Quot.sound"}
found = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    name = m.group(1)
    axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
    found[name] = axs

for name in expected:
    if name not in found:
        sys.exit(f"Missing axiom audit for {name}")
    bad = set(found[name]) - allowed
    if bad:
        sys.exit(f"Disallowed axioms for {name}: {bad}")

src_text = (out / "source" / "Wave4Agent3GlobalClosure.lean").read_text()
for forbidden in ["sorry", "admit", "native_decide", "axiom "]:
    if re.search(rf"\b{forbidden.strip()}\b", src_text):
        sys.exit(f"Forbidden token found in source: {forbidden}")

report = {
    "status": "PASS",
    "module": "Wave4Agent3GlobalClosure",
    "axioms": {k: sorted(found[k]) for k in expected},
}
(out / "kernel-audit.json").write_text(json.dumps(report, indent=2))
print(json.dumps(report, indent=2))
