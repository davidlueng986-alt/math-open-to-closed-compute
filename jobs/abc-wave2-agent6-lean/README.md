# ABC Wave 2 Agent 6 — Lean composition interfaces

Run `bash jobs/abc-wave2-agent6-lean/run.sh 0 1 OUT` in the existing Lean toolbox.
Requires Lean 4.36.0 and Mathlib at `/opt/mathlib4`. The runner copies the exact
source to a temporary file under Mathlib's source root, checks byte equality,
and records compiler version, Mathlib commit, kernel log, `.olean`, theorem names,
axioms and source hashes. Each output theorem must use only the standard axioms.

The source has 14 declarations. They cover the explicit global uniform-composition
interface retaining both open premises, the associated real inequalities and
epsilon conversion, parity/inverse polynomial identities, valuation-cutoff integer
identity, the integer bridge from `a*b*c <= R^2` to `c <= R`, and finite-sum/local-mass
algebra. They do not prove either open global estimate or the abc conjecture.

Before actual hosted execution, the code is a proposed formalization. Only a
successful `result.json` created by the kernel-auditing script grants
`LEAN_VERIFIED` to these exact declarations.
