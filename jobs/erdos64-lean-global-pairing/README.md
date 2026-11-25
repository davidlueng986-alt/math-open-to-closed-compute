# Unbounded parity descent proof attack

This is not the full Erdős 64 proof. Two actual mathematical proof
obligations, not finite SAT experiments:
- BinarySyndrome: a binary linear map of codimension at most one,
  whose image contains an odd-weight vector, must have a nonzero
  kernel or a unit syndrome. Proof via injectivity and two cosets:
  if neither exists the image and its translate by a unit are
  disjoint and cover the ambient space by cardinality. Every
  difference of two units is then in the image; together with an
  odd-weight vector these generate a unit, contradiction.
- PairedShadow: for an actual finite graph, construct the smaller
  SimpleGraph on the selected branches with common midpoints.
  The no-power hypothesis excludes a rectangle (C4), which proves
  uniqueness of midpoints and degree preservation by an injection.
  Each midpoint has exactly two selected neighbors. This proves
  noncollision of all cycle lifts, so the genuine graph-level
  SafeStep follows from the existing checked Shadow module.

The pair-selection hypothesis and degree/cardinality conditions
are explicit; they are not claimed unavoidable for arbitrary graphs.
No `sorry` or axiom used deliberately. Check actual CI logs; initial
elaboration may fail and require repair. This proves the global
reduction interface for all finite orders if kernel verification
succeeds, rather than just numerical arithmetic or conditional
existence of a graph supplied by an external solver.
