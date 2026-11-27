# Verification of the Hadamard closure DAG

The Hadamard conjecture asks for a square sign matrix with orthogonal columns at every order $4t$ for $t>0$. The closure DAG records an all-order construction as the positive answer and a single unrestricted counterexample as the negative answer. Both answers remain open. [DAG and task handoff](closure-dag/README.md) · [Connecting proofs](closure-dag/lemmas.md)

## Reproduce the checks

From the root of the compute repository, use Python 3.10 or later and Lean 4.36.0. The GitHub workflow pins Lean and checks the downloaded archive's checksum. [GitHub workflow](../../.github/workflows/hadamard-all-orders.yml) · [Lean installer](../hadamard-2396-399/install_lean.sh)

```bash
python3 jobs/hadamard-all-orders/closure-dag/check_dag.py --check-tasks
python3 -B jobs/hadamard-all-orders/closure-dag/render.py --check
python3 -B jobs/hadamard-all-orders/closure-dag/verify_pivot.py
python3 -B jobs/hadamard-all-orders/first-match/verify_first_match.py
python3 -B jobs/hadamard-all-orders/first-match/verify_designs.py
python3 -B jobs/hadamard-all-orders/closure-dag/verify_endgame.py
python3 jobs/hadamard-all-orders/verify.py
```

```bash
set -euo pipefail
lean --version
export LEAN_PATH="$(mktemp -d)"
lean -DwarningAsError=true -o "$LEAN_PATH/Triples.olean" jobs/hadamard-2396-projections/Triples.lean
for module in Assembly Reductions Constructions OuterEnergy Rounding
do
  lean -DwarningAsError=true -o "$LEAN_PATH/$module.olean" "jobs/hadamard-all-orders/$module.lean"
done
for module in Lattice PairDefect SwitchParity Coverage45 Star1195
do
  lean -DwarningAsError=true -o "$LEAN_PATH/$module.olean" "jobs/hadamard-all-orders/first-match/$module.lean"
done
```

The graph checker validates node and task references, rejects dependency cycles and checks the separation of the affirmative and negative conclusions. It checks that results marked `PROVED` or `PUBLISHED` cite evidence and satisfy the declared `all_of` and `any_of` dependencies. `CHECKED` diagnostics remain outside closure ancestry. The local evidence paths must resolve to repository files. External citations and mathematical composition statements need expert review. The checker reports readiness for an open, unclaimed task when its listed prerequisites are established. A synthesis card also needs the target's mathematical prerequisites established. Every open leaf must have a card. With `--check-tasks`, each card in the JSON must have a corresponding Markdown heading. Update `dag.json` to change the graph or cards, then run `python3 -B jobs/hadamard-all-orders/closure-dag/render.py` to regenerate the views. [Checker](closure-dag/check_dag.py) · [Graph reference](closure-dag/GRAPH.md) · [Task cards](closure-dag/TASKS.md)

## Lean statements and quantifiers

Write $P_j(t)$ for the existence of a single witness with an outside design, the inside and mixed counts at width $j$, and row capacities. For a row with deficit $u$ and $s$ slots left, appending a binary entry $z$ changes the pair to $(u-z,s-1)$. Under $0\le u\le s$, Lean proves the updated bounds are equivalent to the two boundary rules $u=0\Rightarrow z=0$ and $u=s\Rightarrow z=1$. This covers the one-slot case. The fixed-witness theorem adds the exact size and all intersection equations and characterizes when the appended family is admissible. Lean also checks that row capacities hold for any binary family at widths $j<t$. [Capacity and fixed-witness theorems](Rounding.lean)

Restricting an admissible family to fewer columns preserves capacity and all remaining counts. Given an outside design at fixed $t\ge5$, Lean proves

$$
\left( \forall j<2t-8,\ P_j(t)\Rightarrow P_{j+1}(t) \right)
\quad\Longleftrightarrow\quad P_{2t-8}(t).
$$

Each stage implication permits both witness families to change. Its reverse direction uses the terminal witness restricted to the required width. Fixed-witness binary extension would be a stronger sufficient result. Lean's `fractional_next` proves the exact integer numerators of a feasible fractional column and `from_rounding` takes the unresolved integral step family as a hypothesis. The covered odd multipliers and seven-column completion also enter `from_rounding` as explicit hypotheses. The axiom audit of the new statements reports `propext`, `Classical.choice` and `Quot.sound`. [Rounding statements](Rounding.lean) · [Published completion theorem](https://doi.org/10.1016/0097-3165(80)90028-X)

## First-column certificates and the 45-power family

- Lean verifies exact signed counts, the two-row defect, binary existence at overlap $t-1$, and universal compatibility for any binary certificate with integral coefficients summing to two. A separate Lean arithmetic proof excludes both direct Paley tests and every consecutive-product order throughout the unbounded 45-power progression. The conference-matrix existence theorems and the star construction are cited and proved in the research record. [Lattice](first-match/Lattice.lean) · [Binary columns](first-match/PairDefect.lean) · [Family arithmetic](first-match/Coverage45.lean) · [Written proofs and primary sources](first-match/README.md)
- The independent H44 checker reconstructs both archives and every shared vector. The design replay builds H92 and checks every column pair, exhausts the switched order-28 designs, and enumerates residual word classes, the three orbits at degree 1194 and all 149 compressed Gram determinants at degree 1195. Lean checks the latter square obstructions. [Finite Lean exclusion](first-match/Star1195.lean) [Atlas verifier](first-match/verify_first_match.py) · [Design verifier](first-match/verify_designs.py)

## Written reductions and finite controls

- **Pivot and compatibility.** The positive and negative pivot halves each have $2t-1$ rows. On the complemented half the identity $(J-B)^{\mathsf T}(J-B)=J+B^{\mathsf T}B$ uses the column sums $t-1$. In both directions, the mixed counts identify equal selector signatures and the inside pair counts identify adjacency. A single pair of outside matrices must support the entire clique. For the threshold clique, assembly uses the outside, inside and mixed equations, followed by published completion. The finite replay round-trips all 62 pivot choices at orders 20, 44 and 60 and checks full cliques of size 9, 21 and 29. At order 20, direct enumeration of all 43,758 size-eight columns agrees with the pivot graph's 9 valid vertices and 36 edges. [Connecting proofs](closure-dag/lemmas.md) · [Exact pivot replay](closure-dag/verify_pivot.py) · [Lean assembly](Assembly.lean)
- **Codimension eight.** Rational row reduction computes the lift from eight free coordinates, giving 128 sign tests after global sign. The squared sign equations lie in the span of the constant and 28 pair characters. Testing a basis of their rational coefficient rows preserves all those equations. The replay independently recovers the lift from the integral scaled projector and checks the finite row-type alphabet, norm and multiplicity identity. Direct sign enumeration confirms that twelve Paley columns at order 20 have eight individual extensions up to sign and that the four repeated-row columns at order 12 have zero. The coefficient ranks are 12 and 4, and the respective inputs have 20 and 12 distinct projected row types. Each output applies to its specific input matrix. [Connecting proofs](closure-dag/lemmas.md) · [Exact endgame replay](closure-dag/verify_endgame.py)
- **One-column replacement.** Deleting the last of the four order-12 columns leaves a nine-dimensional kernel. Its 256-pattern test agrees with direct sign enumeration and finds 82 sign vectors up to sign, including 1,296 unordered orthogonal pairs. Each pair extends the three retained columns to five, the seven-column completion threshold at order 12. The original four-column prefix has zero direct extensions. [One-column replacement proof](closure-dag/lemmas.md#one-column-replacement) · [Exact endgame replay](closure-dag/verify_endgame.py)
- **Full-order implications.** The regular-switch energy calculation tracks one fixed pair of balanced matrices at a time. The unproved descent assertion must cover every required odd multiplier and provide a finite path for each relevant state. The commuting construction requires the displayed identities on one jointly labelled pair. An unrestricted disproof at a chosen order needs to exclude every allowed incidence decomposition, and a cutoff-based proof needs a matching all-order theorem beyond the same cutoff covered by its finite certificates. [Connecting proofs](closure-dag/lemmas.md)
- **Existing witnesses.** The incidence replay checks the rational extension identities on prefixes of known solutions and an exact fractional vertex of the order-20 polytope. It also checks all 1,788,886 pairwise products in the order-1892 Scarpis example and all 714,610 pairwise products in the order-2396 width-1196 witness. The universal construction and the square witness at order 2396 remain open. [Witness replay](verify.py) · [Original all-order notes](README.md)
