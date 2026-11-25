# Full-cycle automaton and extended three-port substitution

Prior run 45460619963: 21/21 jobs succeeded. The 3..17 order census found four
gadget isomorphism classes (orders 3,7,7,15), giving 9 labelled spectral
states including the singleton. All 27 connected cubic bases of orders
4,6,8,10 were UNSAT with checked DRAT for this catalogue. The smaller 6-state
catalogue was independently UNSAT on the same bases. This is not closure.

New exact encoding: for a base cycle of length r, each vertex choice gives
the set of possible internal path lengths. The DP state is the mask of ALL
possible sums, initially {r}. Each transition is the Minkowski sum with the
chosen local spectrum; final states accept exactly when no power of two >=4
occurs. Backward viability prunes impossible suffixes. SAT implications from
an active node and each possible choice enforce the deterministic next node.
The asserted root forces an accepting path. This allows a whole cycle to
be added at once rather than many individual path-witness cuts. If the
diagram exceeds its cap the fallback forbids just one invalid full word.
The proof generator rebuilds the CNF from the trace and checks DRAT.
Direct integer sumsets independently check the diagram language for every
word of lengths 3 and 4. A prospective counterexample is expanded and all
dyadic simple cycles checked independently. Larger cycle diagram correctness
uses the exact induction on the sumset state, not a finite extrapolation.

Domain: all connected cubic bases of order 12 and 14; all triangle- and
4-cycle-free connected cubic bases of order 16; fixed published 24/26
no-C4/C8 corpus. No inference about other graphs or larger gadgets.
