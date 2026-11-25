# ERDOS-64 Wave 2 Agent #3 — Lean 4.36.0 Structural Theorems

Formalizes and kernel-verifies 9 unconditional all-order theorems on `MinimalBad G` in Lean 4.36.0 (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`) using the pinned GHCR Lean image (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`):

- `minimal_bad_no_c4`, `unique_common_neighbor`, `minimal_bad_no_high_adj`
- `universal_dyadic_path` & `unified_bipartite_exclusion` (Wave 1 theorems)
- `cubic_dist2_dyadic_path`, `cubic_all_nonadj_dyadic_path`, `cubic_p3_dyadic_plus_two_cycle`, `defect_dist2_dyadic_path` (NEW Wave 2 theorems)
