# Erdős #64 — Wave 2 Agent #5 Lean 4.36.0 Structural Weapons

Formalizes and verifies (under Lean 4.36.0 + Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, standard axioms only, `-DwarningAsError=true`) nine unconditional all-order theorems on `MinimalBad(G)`:

1. `IndependentExpansion.lean`:
   - `indep_neighborhood_expansion`: $|N(I)| \ge |I| + 2$ for every nonempty independent set $I \subseteq V_3$ with $N(I) \subseteq V_{\le 3}$.
   - `indep_syndrome_no_kernel`: $\ker(A_I) = \{0\}$ over $\mathbb{F}_2$.
   - `dual_kernel_non_j3_ge_two` (NEW Wave 2): Every $S \in \ker(A_I^T)$ meeting $J_3$ satisfies $|S \setminus J_3| \ge 2$ in cubic `MinimalBad(G)`.
2. `ConnectivityAndCuts.lean`:
   - `minimal_bad_no_cut_vertex`: 2-vertex-connectivity of `MinimalBad(G)`.
   - `minimal_bad_two_edge_connected`: 2-edge-connectivity (connectedness + no bridges) of `MinimalBad(G)`.
3. `IdentificationAndContraction.lean`:
   - `universal_dyadic_path`: $\operatorname{dist}_G(x, y) \ge 3 \implies \exists$ simple $x$–$y$ path of length $2^k$ ($k \ge 2$).
   - `cubic_dist2_dyadic_path` (NEW Wave 2): In cubic `MinimalBad(G)`, $\operatorname{dist}_G(x, y) = 2$ with common neighbor $c_0 \implies \exists$ simple $x$–$y$ path of length $2^k$ ($k \ge 2$) avoiding $c_0$.
   - `cubic_nonadj_dyadic_path` (NEW Wave 2): In every cubic `MinimalBad(G)`, EVERY non-adjacent pair has a simple $2^k$-path ($k \ge 2$).
   - `edge_contraction_dyadic_plus_one` (NEW Wave 2): Every triangle-free edge in `MinimalBad(G)` lies on a simple $(2^k + 1)$-cycle ($k \ge 2$).
