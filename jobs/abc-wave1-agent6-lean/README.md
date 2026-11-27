# Agent 6: Lean 4.36.0 structural and quantifier audit

Run with the repository's Lean toolbox, whose cached Mathlib checkout is `/opt/mathlib4`:

```bash
bash jobs/abc-wave1-agent6-lean/run.sh 0 1 /tmp/abc-agent6
```

The 24 named declarations cover Frey polynomial identities, the squaring transform, height lower-bound algebra, both epsilon conversions in cross-multiplied form, the balanced cube-excess algebraic step, the scalar normalization budget, exact Reyssat arithmetic, actual radical support/positivity, and the exact quantified condition sufficient to refute abc.

`ArithmeticABC` uses an actual finite-prime-product definition of the radical of a positive natural number. It is not an abstract unconstrained parameter. The countersequence theorem leaves `UnboundedRatioAt e` explicit. There is no asserted proof of that hypothesis.

The runner checks the requested Lean version, compiles through the kernel, prints and audits the axiom closure of every named theorem, and accepts only `propext`, `Classical.choice`, and `Quot.sound`. It rejects placeholders, custom axioms and native-decide shortcuts. A successful artifact contains source/log hashes and an `.olean` file.

This file does not formalize elliptic-curve conductor/minimality, Faltings-height comparison, the full abc/Szpiro equivalence, or IUT. The numerical radical value for the Reyssat triple is independently certified by Agent 4; this Lean file proves its prime support arithmetic and the exact integer quality comparison, not an evaluation of the deliberately naive radical definition on its enormous radicand.

No successful hosted compilation is claimed until `result.json` exists with the kernel audit completed.
