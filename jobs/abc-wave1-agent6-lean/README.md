# Agent 6: Lean 4.36.0 structural and quantifier audit

Run with the repository's Lean toolbox, whose cached Mathlib checkout is `/opt/mathlib4`:

```bash
bash jobs/abc-wave1-agent6-lean/run.sh 0 1 /tmp/abc-agent6
```

The 24 named declarations cover Frey polynomial identities, the squaring transform, height lower-bound algebra, both epsilon conversions in cross-multiplied form, the balanced cube-excess algebraic step, the scalar normalization budget, exact Reyssat arithmetic, actual radical support/positivity, and the exact quantified condition sufficient to refute abc.

`ArithmeticABC` uses an actual finite-prime-product definition of the radical of a positive natural number. It is not an abstract unconstrained parameter. The countersequence theorem leaves `UnboundedRatioAt e` explicit. There is no asserted proof of that hypothesis.

The runner checks the requested Lean version, compiles through the kernel, prints and audits the axiom closure of every named theorem, and accepts only `propext`, `Classical.choice`, and `Quot.sound`. It rejects placeholders, custom axioms and native-decide shortcuts. A successful artifact contains source/log hashes and an `.olean` file.

This file does not formalize elliptic-curve conductor/minimality, Faltings-height comparison, the full abc/Szpiro equivalence, or IUT. The numerical radical value for the Reyssat triple is independently certified by Agent 4; this Lean file proves its prime support arithmetic and the exact integer quality comparison, not an evaluation of the deliberately naive radical definition on its enormous radicand.

Hosted verification succeeded in [run 45960558321](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45960558321), job `140377163268`, at source commit `d6bb84b3d382ef3412a1e7e7a4ff540d4c1fe87a`. The [published result and full axiom log](https://github.com/davidlueng986-alt/math-open-to-closed-compute/tree/results/runs/abc-wave1/45960558321/agents/abc-wave1-agent6) record Lean 4.36.0, Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, 24 declarations, and standard axioms only. Source SHA256: `7a37b2715a931a983cd056c2b679dc285b3f0ac3cde62526174bc05ce154feb9`.

The earlier run `45960187601` stopped before checking proofs because its source lay outside the Mathlib compilation root. The runner now copies and byte-compares its source into a unique temporary path inside that root. This corrected runner produced the successful result above. The original abc conjecture remains `BLOCKED`.
