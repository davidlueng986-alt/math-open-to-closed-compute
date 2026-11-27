# Exact evaluation of a fixed seeded private-endpoint rule

This job evaluates the deterministic rule in
[the research note](https://github.com/davidlueng986-alt/math-open-to-closed/blob/main/research/ERDOS-25/wave3/fixed-gap/seeded-greedy-mechanism.md).
It starts from `(6,0), (10,1), (15,2)` at integer 22, chooses the
smallest exact conditional Haar increment among the legal canonical
endpoint moduli, and breaks ties by the largest modulus. The mathematical
rule has no terminal cutoff. The public job truncates its evaluation at
1200 or after 480 seconds, whichever occurs first; a runtime limit
preserves the last completely evaluated prefix.

The immediate finite question is whether the rare conditional fiber can
propagate beyond the initial parent `[2] mod 5`. The exact first escape
is `(n,q,a)=(389,377,12)`, with `377=13*29`. The new run starts from
scratch, reproduces that event, and continues the parent structure.
This is a falsifiable structural test, not a density estimate.

The actual deleted union of the complete infinite rule is cofinite:
at every surviving integer `n`, `q=n, a=0` is a legal fallback. A
negative resolution would therefore follow if the rule's infinite
Haar survivor budget were proved positive. In chronological order,
write `h_j=e_j/delta_(j-1)` for its relative hazard. Subject to no
finite full cover, the needed assertion is `sum h_j < infinity`.
The finite computation does not prove it.

`rare_fiber_selector.py` (mirrored from the fixed-gap directory)
uses exact Python `Fraction` arithmetic and recursive CRT decomposition.
The frozen search SHA-256 is
`6d136a516818d5e646887de8f3a565dafedce4e18ddd43f856cd9dab5656a3ff`.
`validate_result.py` independently checks distinct moduli, actual
activation, every private endpoint, complete deletion of the evaluated
integer interval, exact telescoping of recorded rational increments,
and the first escape. It independently enumerates the seed and first
increment; it does not separately recompute every later Haar measure.
The exact scope is included in the JSON output.

The workflow uses one GitHub-hosted job, has a 12-minute timeout, and
uploads source hashes, the commit, logs, the exact prefix and validation.
Public artifact files will also be retained with the research record.

**Erdős #25 remains OPEN.** The source is ordinary exact computation,
not a Lean proof of an infinite statement.
