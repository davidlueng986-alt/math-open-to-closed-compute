# Erdős #25: proof-wave verification

This job verifies the decisive finite prime-signature lemmas in the new
bounded-gcd-overlap reduction and replays existing finite proof components.
It does not prove the original Erdős #25 conjecture.

Sources:

- `BoundedGcdSignature.lean`: this wave's actual prime-factor-list signature,
  divisibility, rank, injectivity, and conditional finite reciprocal comparison.
  The largest-prime lower bound and convergent infinite series remain ordinary
  mathematical proofs. The natural-density implication imports the separately
  reviewed bounded-Ω density theorem.
- `AffineResidues.lean` and `BoundedQuotient.lean`: exact source from research
  repo commit `9a0f92673e5f115d870159f4ea2631bb64302d5d`, recompiled in the
  pinned Lean 4.36.0/mathlib toolbox. These are four finite/algebraic lemmas,
  not formalizations of the infinite density theorems.
- `check_two_primes.py`: exact finite-CRT replay from research repo commit
  `eb8fdf83d266b33aadf80f947fd220b663f04b38`. Its 720 finite cases check
  identities and inequalities used in the two-prime argument; they do not
  establish an infinite limit or original closure.

Each Lean module prints transitive axioms. The verifier rejects `sorryAx` and
any axiom beyond `propext`, `Classical.choice`, and `Quot.sound`. Logs, source
SHA-256 hashes, toolchain version, and mathlib revision are retained as artifacts.
Jobs have finite time limits and no schedule is installed.
