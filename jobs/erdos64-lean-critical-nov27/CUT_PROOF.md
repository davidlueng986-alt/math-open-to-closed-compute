# Minimal cubic two-cut completion

## Exact contribution

This formalizes the ordinary minimal-side completion claim recorded in Wave 2.
It is an all-order structural reduction for both cubic low2 terminals,
`C-T-2` and `C-N-2`. It does not exclude either whole terminal.

The application theorem starts with exactly

`MinimalBad G`, `Cubic G`, and `SmallCut G 2`.

It chooses a nontrivial two-cut side A of least cardinality. Its boundary is
exactly two edges a-x and b-y, with four distinct endpoints, and the two
vertices a,b inside A are not adjacent. Let

H = G[A] + ab.

Then H is a strictly smaller simple cubic graph, every nonempty proper cut of
H has at least three edges, H has a power-of-two cycle, and G[A] has none.
Thus every such cycle in H must use its single new edge ab. The relevant
formal theorem is `E64MinimalCut.cubic_minimal_bad_two_cut_normal_form`.

## Proof

1. Well-founded minimization of the cardinality of a SmallCut side provides A.
   Previously verified biconnectivity/bridgelessness of MinimalBad gives at
   least two boundary edges, so there are exactly two. The previously verified
   cut-boundary theorem applied on both sides gives distinct boundary vertices
   a,b and x,y. Every nonempty proper subset T of A has at least three outgoing
   edges: a singleton has degree three; a larger T would otherwise be a smaller
   nontrivial cut side.

2. If a and b were adjacent, remove both from A. Each has exactly one remaining
   neighbor inside A, since its other two neighbors are the other port and its
   exterior endpoint. The remaining subset is nonempty, as otherwise a would
   have degree at most two. Its boundary injects into the two removed ports,
   so it has at most two edges, contradicting the preceding minimality. The new
   edge ab is therefore absent from G[A]. Adding it restores the missing degree
   at each port, while all other vertices keep degree three.

3. Take any nonempty proper subset S of A in H. Choose S or its complement in A
   so that b lies outside the chosen side. Each original G-boundary edge from
   that side either lies wholly in A and remains an H-boundary edge, or is the
   unique exterior edge a-x and is replaced by ab. This mapping is injective:
   an exterior edge cannot collide with an internal edge, because ab was not an
   original edge. Consequently the original boundary, which has at least three
   edges, injects into the completed boundary. Reversing cut orientations treats
   the case in which b belonged to the initially chosen S.

4. H has fewer vertices than G and is cubic, hence Near. The defining global
   minimality of G gives HasPower H. An induced subgraph cannot have a power
   cycle absent from G, so G[A] is power-free.

## Precisely what remains

Let P_A and P_B be the simple port-to-port path-length sets in the two original
cut sides. Completion forces some 2^r-1 in P_A. Separate completion and
identification arguments may force other dyadic or shifted-dyadic lengths.
The missing theorem must force a pair p in P_A, q in P_B with

p + q + 2 = 2^k, k >= 2,

or provide another valid smaller Near counterexample. The completion theorem
supplies a cubic graph with strong connectivity and a prescribed indispensable
power-cycle edge; it does not synchronize exponents between the two sides.

## Verification scope

Source modules: MinimalCutCompletion.lean and CutCompletionApplication.lean.
Dependencies: the existing complete-leaves foundations, Wave 2
ConnectivityAndCuts.lean, and Wave 3 CutBoundaryWeapons.lean.
No finite search, new axiom, admitted theorem, or assumed full leaf exclusion
appears in these sources. Kernel-pass status must be attached only after the
actual GitHub Actions logs and transitive axiom output have been checked.
