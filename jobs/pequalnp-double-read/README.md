# L-meta-2081 order-3 plane incidence circuit

The desk asks for a circuit with at most 64 gates that computes plane incidence and has both formal traces zero at the point-0, line-0 incidence. The standard line-star circuit has 64 gates and both traces are one.

A 65-gate circuit satisfies both trace conditions. Let `A` be the line-0 star and let `B` be the OR of the four points incident to line 1. Replace the OR of the first two stars with `(line_1 ∨ A) ∧ (B ∨ A)`. Distributivity gives `A ∨ (line_1 ∧ B)`, and this substitution adds just one gate. Both factors are false on both singleton backgrounds, because point 0 is off line 1. The conjunction therefore has zero trace in both directions. The other eleven stars also have zero trace in those directions.

The control checks all 52 incidences and all 8,192 assignments formed by taking an arbitrary set of points and every compatible line. These contain every maximal false input. There are 704 maximal false inputs. Monotonicity extends these checks to all Boolean assignments.

## Small replacements

On a single line, synthesis rules out five gates with both traces zero. It finds a six-gate circuit. For two lines, the intersection point is either the marked point or a different point on line 0. The representatives are lines `(0, 12)` and `(0, 1)`. The usual two-star circuit takes nine gates. The eight-gate SAT instances are UNSAT and the initial nine-gate searches reached their conflict budget. The `(0, 1)` ten-gate instance found a circuit; the factored expression above gives a direct construction of that size.

There is a separate argument excluding a nine-gate double-read replacement for either two-line case. There are nine essential inputs, so the live cone has at least eight gates. An eight-gate circuit is read-once. A read-once formula for the connected edge function would have an AND at its root. Since all minterms have size two and the children use disjoint nonempty sets of variables, both children must be ORs of their variables, which would give a complete bipartite graph. The two-line graph is connected and is missing cross edges.

With nine live gates there is exactly one wire with two consumers, by counting the 18 operand uses and the 17 non-output wires. Both flagged variables must feed that wire. Otherwise the variable outside its cone has a unique path to the output, and its formal trace is one whenever flipping that variable changes the output. Let the shared wire be `U`. At the flagged pair, every input outside `U`'s cone is zero. The first reconvergence must be an AND with both paths from `U` consisting only of OR gates. If the reconvergence were OR, an active path from `U` would propagate the nonzero trace. The shared wire is read-once and must change from zero to one on either flagged flip, so its two traces are nonzero. Thus the reconverging expression is `(U ∨ A) ∧ (U ∨ B)`, where either disjunction of side inputs may be empty. Factoring it as `U ∨ (A ∧ B)` saves at least one gate, giving the impossible eight-gate circuit.

This excludes isolated one- and two-line replacements within the corresponding standard gate budgets. The unrestricted 64-gate existence question remains open.

```sh
python -m pip install python-sat==1.9.dev25
python jobs/pequalnp-double-read/control.py
python jobs/pequalnp-double-read/synthesis.py 0 --gates 5
python jobs/pequalnp-double-read/synthesis.py 0 1 --gates 10 --conflicts 300000
```

## Lean verification

`PlaneDoubleRead.lean` proves `PlaneDoubleRead.construct65` in the upstream circuit model. It checks the output for arbitrary Boolean inputs and both trace recurrences. `PlaneDoubleRead.candidate64_is_desk` identifies the 64-gate statement with the posted L-meta-2081 proposition. `PlaneDoubleRead.Desk2082` is its negation. Both 64-gate propositions remain open.

The `pequalnp-double-read-lean.yml` workflow builds the pinned upstream definitions, checks the file with Lean, and audits the theorem dependencies against the upstream checker's axiom list.
