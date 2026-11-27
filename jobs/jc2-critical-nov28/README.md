# JC2 critical algebra, 2026-11-28

`LocalSocleDegree.lean` proves the finite-dimensional nilpotent-chain and
boundary-quotient dimension bound used in the new local-degree argument.
The geometric application is documented in the main research repository.
It is not represented by an unproved analytic axiom in Lean.

The workflow reuses the pinned GHCR Lean/mathlib toolbox, has a 45-minute
per-job limit, treats warnings as errors, scans the exact sources, and
checks the printed transitive axiom dependencies of every audited theorem.
