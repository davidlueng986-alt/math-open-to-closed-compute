# ABC Wave 1 Agent 2 — arithmetic bounds and obstruction checks

Run `bash run.sh 0 1 /tmp/abc-agent2` with Python 3. No third-party packages,
network, SageMath, solver, or Lean installation is required for this job.
It is suitable for the shared manual GitHub Actions runner, well below six hours.

Checks include the balanced cube-excess inequality, the min-largest-prime
bound, product-of-exponents tail control, the explicit infinite-family
obstruction to a too-strong cube-excess hypothesis, and a published smooth
`n^2+1` example. Infinite statements have written proofs in the research
report; finite checks are explicitly not claimed to prove abc or its negation.

No unspecified constant in Stewart--Yu or Pasten is fitted or estimated.
The illustrative envelope calculation sets kappa=1 solely to display scales.
