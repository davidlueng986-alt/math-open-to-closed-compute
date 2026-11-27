# ABC Wave 3 Agent 4: Fermat square-area descent

Reproducible Lean 4.36.0 kernel compilation on Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. One shard; no paid or scheduled resources.

The source proves primitive square-area impossibility by an actual decreasing hypotenuse construction and derives the difference-of-fourths theorem for coprime odd/even inputs. The plus-sign theorem `not_fermat_42` is not used.

Run `bash run.sh 0 1 <output-directory>` inside the repository's pinned Lean container. `audit.py` verifies all four public theorem axiom lists and requires the compiled `.olean`. Mathematical and kernel status must be read from the actual run outcome, not this README.

No abc closure is claimed.
