# ABC Wave2 Agent5 — joint height budget

Run `bash jobs/abc-wave2-agent5-height/run.sh 0 1 OUT`.

The hosted job requires the existing Sage toolbox. It checks 32 exact global minimal discriminants and conductors for the explicit semistable family y²+xy=x³+x+47m, in addition to finite exact invariant identities, factor-exponent budgets and rational model composition checks. Locally, an environment without Sage may run the standard-library part, but records `sage_available:false` and zero geometric checks. A GitHub Actions job without Sage fails rather than silently skipping this requirement.

No finite check proves the classical local criterion or either of the two remaining global estimates. No abc closure or Lean verification is claimed. Full written proofs and scope are in main-repo `research/ABC/wave2_agent5/REPORT.md`.
