# Certificate-producing global descent engine

This is a real implementation of the all-order safe-descent results in
jobs/erdos64-global-compression/README.md, rather than a fixed-order scan.
The local exact-spectrum rules include the independently checked symmetric
7 -> 6 and 15 -> 14 replacements. They are legal only when there is no
existing exceptional low-degree vertex outside the replaced block.

## Exact all three-edge cut discovery

For any finite connected graph G, choose a spanning tree and form the
fundamental cycle basis over F2. Assign each edge the bit vector describing
which basis cycles contain it. A set of edges is a cut (delta(S)) iff the
xor of its signatures is zero: the forward implication follows from even
cut/cycle intersection. For the converse, assign to each vertex the parity
of selected edges on its tree path from the root. Tree-edge membership
agrees with whether endpoint parities differ. For every non-tree edge,
the corresponding fundamental-cycle parity gives the same equivalence.
Consequently any triple with zero xor is exactly a three-edge cut.

Find all triples using a signature hash table and pair lookup. For each
triple, remove its three edges and inspect each connected component with
exactly that boundary. Match each induced catalogue gadget by exact graph
isomorphism, checking all external ports are distinct and every old
nontrivial-block vertex is cubic. This discovers all admissible catalogue
blocks in any finite connected simple graph, no order cap.

## Exact block selection and reconstruction

A SAT variable for each discovered block; at most one selected block at
each vertex; each original edge must have an endpoint in some selected
block. The latter is exactly independence of leftover singleton vertices.
A positive model gives the global mixed 2x lifting reduction; otherwise
try a legal single-block equal-length replacement. Each step strictly
reduces order. Record the actual old/new graph, block vertices, ordered
ports and cycle scale. An actual power cycle found in a smaller graph is
lifted back through every step with explicit vertex-disjoint paths and
checked against original edges and exact cycle length.

Parallel quotient edges give a direct witness using the catalogue
spectra, not an invalid simple-graph quotient. If no rule or witness is
found, the result is NO-FURTHER-RULE-OR-WITNESS, not power-free certification.
The remaining missing theorem is unavoidability of these or other
reductions in an arbitrary minimal near counterexample. In particular
the present catalogue has triangles, so arbitrary high-girth residuals
need other ideas.
