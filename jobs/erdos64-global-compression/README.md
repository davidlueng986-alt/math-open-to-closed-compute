# Global safe descent for three-port blocks, arbitrary graph order

Original problem remains OPEN. The target is any finite simple graph of
minimum degree at least three. We use the equivalent near formulation
(Ducoffe–Dumitru 2026, Theorem 4.2): allow at most one low-degree vertex,
require a degree-at-least-three vertex. A minimum-order power-free near
counterexample is enough. This is NOT another bounded original-graph census.

## Theorem 1: exact spectrum domination, local replacement

Suppose a near graph G has a proper connected induced block K with exactly
three external edges, all at distinct internal ports. Replace K by a
smaller connected power-free graph H with three distinct labelled ports,
reattaching the same three external edges. Require the resulting graph
G' to be simple and near, and for each pair of ports require the entire
simple-path length spectrum of H to be a subset of that of K.
Then every power-length simple cycle of G' has a simple cycle of the
same length in G. Proof: a simple cycle crosses the 3-edge boundary an
even number of times, hence zero or two. A cycle inside H cannot be a
power. A cycle outside H is unchanged; a crossing cycle uses one simple
port-to-port path inside H. Replace that path by an equal-length path
inside K; the outside path is disjoint. Thus G' is a smaller near
counterexample if G is power-free. In a minimum-order near counterexample
no such spectrum-dominated replacement can occur.

Concrete exact example: symmetric 7-vertex gadget FCptO, ports (1,2,3),
has all three spectra {2,3,4,5,6}. Replace by 6-vertex graph EZEG,
ports (0,1,4), spectra {2,3,4,5}, {2,3,4}, {2,3,4,5}.
Its internal simple cycles have lengths 3,5,6. With external edges
all vertices have degree 3 except vertex 5 of degree 2. Therefore a
minimum-order near counterexample that is cubic cannot contain this
induced 7-block with the stated 3-edge boundary. This is a local
obstruction at arbitrary order, not a claim that every graph has such
a block. If an existing defect lies outside K, the 6-block would create
a second defect and is not automatically legal.

## Theorem 2: arbitrary mixtures, simultaneous dyadic dominance with slack

Partition G into connected induced blocks of the following types:
singleton (any degree), triangle (three degree-two ports), either of the
two 7-vertex power-free 3-port gadgets, or the 15-vertex 3-port gadget
listed in catalogue.json. Each nontrivial block has exactly one external
edge at each of its three ports; all other vertices are cubic.
Assume at least one nontrivial block. Assume the singleton vertices
are independent in the block quotient (or more generally every simple
quotient cycle has at most as many singleton blocks as nontrivial blocks).
An exceptional low-degree vertex, if present, is a singleton.

Replace triangles by singletons, both 7-blocks by triangles, and the
15-block by the symmetric 7-block; keep the port correspondence arbitrary.
Keep each external edge. Call the new graph R.

Claim: if G is power-free and near, R is strictly smaller and is also
simple, power-free and near. Proof:
(1) In a power-free G there cannot be two external edges between the
same pair of blocks. The exact catalogue intervals show that the sum
of the two port path lengths plus two includes a power of two for
every pair of nontrivial blocks and for a singleton/nontrivial pair.
Two singleton blocks cannot have parallel edges in a simple graph.
Since blocks are induced, no external self-loops. Therefore the block
quotient is simple. The replacement graph is simple; degrees are
preserved at singletons, and all new block vertices are cubic.
(2) A simple cycle of R either stays in one block (no power there) or
crosses each visited nontrivial block exactly twice. Thus it projects
to a simple cycle of the quotient. Each singleton contributes 1 to
its length (the outgoing external edge). At a compressed nontrivial
block suppose its path length is l, giving contribution q=l+1.
For each possible l in the replacement, the original port spectrum
contains both 2*l+1 and 2*l+2:
  triangle -> singleton: l=0, original 1,2;
  7 -> triangle: l in {1,2}, original paths 3..6 available;
  15 -> symmetric 7: l in {2,3,4,5,6}, original paths 5..14 available.
Including the external edge, the original block contributes 2*q or
2*q+1, independently of other blocks. An unchanged singleton contributes
1 instead of 2, a deficit of one. Along the quotient cycle, the number
s of singletons is at most the number b of nontrivial blocks (for
independent singletons, cyclic successor maps singleton positions
injectively into nontrivial block positions). Choose the +1 option at
exactly s of the b blocks. The total original length is exactly twice
the smaller cycle length. The independent chosen simple paths in
disjoint blocks, connected by distinct external edges, form a simple
cycle. So any power cycle in R gives a power cycle in G, contradiction.
(3) Each nontrivial block shrinks (3->1,7->3,15->7); at least one exists.
Consequently R has fewer vertices. In a minimal near counterexample
such a partition cannot occur. The proof works at every order and
with arbitrary degrees of singleton vertices, not merely cubic bases.

This strictly extends the pure triangle vertex-cover and homogeneous
pentagon-factor descent to mixed spectral compression. It also yields
a terminating certified global reduction process: repeatedly find
either a local spectrum-dominated legal replacement (Theorem 1) or
a spanning partition satisfying Theorem 2; replace and preserve its
lift certificate. If no rule applies, the irreducible residual is not
proved power-free and is not solved. There is NO claim of unavoidability.

## Evidence

Catalogue is extracted from input-domain artifact 14996329464 of prior
run 45559488174 (three-port census run 45460619963). verify.py checks
all spectra, internal cycles, all 216 possible labelled parallel-edge
port cases (number reported at runtime), and constructive arbitrary
mixed-base controls using exact cycle lifts. A separate nauty/C++ census
checks smaller one-defect subcubic replacements through 14 vertices;
it is a search for *universally valid local rules*, not for bounded
original counterexamples. Lean verifies the unbounded length budget
and exact doubling arithmetic, not the whole graph construction.
The general graph correspondence is proved above. No novelty or priority
claim; the previous literature includes uniform dyadic subdivisions
and triangle reductions. The original full unavoidability gap remains.
