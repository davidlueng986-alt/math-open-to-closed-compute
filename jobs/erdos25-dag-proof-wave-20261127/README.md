# Erdős #25: proof-wave verification

This job checks finite prime-signature lemmas and replays existing finite proof
components. The original Erdős #25 problem remains OPEN. The ordinary density
theorems and the unrestricted infinite limit are outside this formal scope.

## Sources and proof scope

- `BoundedGcdSignature.lean` formalizes the actual prime-factor-list signature,
  divisibility, rank, injectivity, and a finite reciprocal comparison with an
  explicit product-bound hypothesis. The largest-prime bound, infinite series
  and density bridge are ordinary proofs. The signature argument was already
  present in Plasma AI's earlier research; this wave makes no priority claim.
- `AffineResidues.lean` and `BoundedQuotient.lean` preserve the theorem code from
  research commit `9a0f92673e5f115d870159f4ea2631bb64302d5d`. The compiled copies
  have one additional trailing newline. They provide four finite/algebraic
  lemmas and were recompiled in the pinned Lean 4.36.0/mathlib toolbox.
- `check_two_primes.py` replays the checker from research commit
  `eb8fdf83d266b33aadf80f947fd220b663f04b38`, with only trailing-newline
  normalization. Its 720 cases check finite identities and inequalities.

Each Lean module prints transitive axioms. The verifier rejects `sorryAx` and
any axiom beyond `propext`, `Classical.choice`, and `Quot.sound`. Exact compiled
source hashes, logs, Lean version and mathlib revision are saved as artifacts.

## Observed results

- Run [45993326807](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45993326807): the two original Lean modules and 720 CRT cases passed;
  the first signature attempt failed with two elaboration errors.
- Run [45993861302](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45993861302): the corrected signature module passed all six axiom-closure checks.
  Only that changed module was recompiled in this run.
- The ten accepted declarations depend only on standard axioms. The downloaded
  artifact archive digests and all four integrated source hashes were checked.

Permanent source audit, ordinary-proof scope and verification records are in
[the integrated research report](https://github.com/davidlueng986-alt/math-open-to-closed/blob/2ad1ebf303bfd646bb3512a3ae561295f05d1a19/research/ERDOS-25/2026-11-27-dag-proof-wave.md).
The stronger already-known squarefull-kernel theorem is attributed there.

Jobs have finite time limits. Manual dispatch reruns the proof matrix; normal
proof pushes rerun affected modules. No periodic schedule is installed.
