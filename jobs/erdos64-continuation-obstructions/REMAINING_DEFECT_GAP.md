# Exact remaining one-defect gap after the new full core exclusions

## What a complete suppression proof still needs

Let G be a nonbipartite MinimalBad Near graph with degree-two vertex w and
cubic neighbors a,b. If a,b are nonadjacent, suppress w by replacing awb
with ab. The resulting graph has one fewer vertex and minimum degree at
least three. Minimality therefore produces a power cycle. Such a cycle
must use the new edge, since a cycle avoiding it is already in G.

Thus suppression proves only that G-w has a simple a-to-b path of length
2^k-1. Its lift through w has length 2^k+1, which is allowed. In the
bipartite case this odd path is impossible, which is why that entire
family is already excluded. For the remaining nonbipartite case there is
no contradiction. Neither suppressing nor moving the defect preserves the
power-free condition without a new path-spectrum theorem.

Vertex identifications yield power-length paths from w to other vertices,
including paths forced to leave through either neighbor in the situations
already recorded in the Nov24 one-defect note. Equal power lengths alone
are insufficient: intersections can prevent their union from being a
simple power cycle. A new proof must use the full requirement that every
nondefect vertex has degree at least three, or a structural consequence
stronger than the root-path obligations.

## Explicit obstruction to a proposed standalone collision theorem

The biconnected graph on {0,1,2,3,4,5} with edges

    01,02,14,23,34,35,45

has a degree-two root 0 and simple length-four paths from 0 to every other
vertex:

| Target | Path |
|---|---|
| 1 | 0,2,3,4,1 |
| 2 | 0,1,4,3,2 |
| 3 | 0,1,4,5,3 |
| 4 | 0,2,3,5,4 |
| 5 | 0,1,4,3,5 and 0,2,3,4,5 |

The only target at distance at least three is 5, and its two displayed
paths start in different root directions and end through different edges.
Nevertheless, this graph's complete cycle-length set is {3,5,6}: it is
the theta graph with branch vertices 3,4 and branch-path lengths 1,2,4.
It has no power-of-two cycle.

This is NOT an original counterexample: vertices 1,2,5 also have degree
two. It refutes only the standalone implication from the root-path
saturation conditions to a simple power-cycle collision. The obstruction
explains why omitting the global degree constraints would leave a false
proof step.

Attempting to repair these three additional degree-two vertices by the
six-vertex-gadget ring construction fails at all orders; see the complete
ordinary alternating-cycle proof in SIX_VERTEX_GADGET_OBSTRUCTION.md.

## Status

No additional nonbipartite S/H low2 or low3 terminal leaf has been excluded
by this continuation. The full formal core exclusions remain valid but do
not fill this spectral/intersection gap. No new Lean theorem is submitted
for these incomplete routes.
