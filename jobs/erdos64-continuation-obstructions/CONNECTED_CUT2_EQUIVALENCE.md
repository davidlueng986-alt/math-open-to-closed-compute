# Exact strength of the connected two-port theorem

## Theorem: without global minimality, the connected-side two-cut target is equivalent to the original problem

Let EG be the exact original Erdős–Gyárfás conjecture for finite simple graphs of minimum degree at least 3.

Let CUT2 be the assertion that every finite connected simple graph H of minimum degree at least 3, admitting a partition A,B with both induced sides connected and exactly two crossing edges having four distinct endpoints, has a power-of-two simple cycle.

Then EG if and only if CUT2.

The forward implication is immediate. For the reverse, assume EG false, and choose a connected counterexample F (a connected component of any counterexample suffices). Take five disjoint copies F_0,...,F_4. Choose a vertex v_i in each copy, and add the five edges v_i v_{i+1}, indices modulo 5, forming a C5 between the selected vertices.

All old vertices retain minimum degree at least 3; the selected vertices gain two. The graph is simple and connected.

Every simple cycle is either contained in one F_i or is exactly the new C5. Indeed, each F_i meets the rest of the graph only at v_i. A simple cycle cannot enter F_i through v_i, traverse some nonempty part of it, and exit back through v_i while also visiting the rest, because that repeats v_i. Therefore a cycle meeting multiple copies uses no non-root vertex, and must be the base C5. No cycle has power-of-two length.

Let A contain the vertices of F_0 and F_1, and B those of F_2,F_3,F_4. Both induced sides are connected. Exactly two edges cross: v_1 v_2 and v_4 v_0. Their endpoints are all distinct. Thus H contradicts CUT2. QED.

The construction works at arbitrary order; no search or unproved graph-theoretic result is used.

## Consequence for the current low2 attack

Merely adding connected sides to the standalone two-port spectral theorem does not make it an easier target: it still proves the full original. The five-copy witness has cut vertices and is not globally order-minimal. A potentially easier minimal-counterexample theorem must retain and exploit the global MinimalBad hypothesis, or a genuinely stronger structural hypothesis such as biconnectivity of the full graph and relevant side atoms.

This observation does NOT close a leaf. It prevents replacing the six low2 leaves by an apparently smaller but logically full-strength problem and counting that as a reduction in mathematical difficulty.

## Critical degree-upgrade audit

The valid observation remains: the two original ports of a defect-free side of a minimal matching 2-cut must both be cubic. It cannot be upgraded to “all internal vertices of the side are cubic” using only degree constraints, C4-freeness and absence of a Near subgraph.

An explicit obstruction is constructed from the Heawood graph with point labels 0,...,6 and line labels 7,...,13, with line 7+j incident to points j,j+1,j+3 modulo 7. Delete edge (0,7), and contract disjoint edge (2,8), retaining label 2 for the merged vertex.

The graph has 13 vertices. Vertices 0,7 have degree 2; vertex 2 has degree 4; all ten others have degree 3. It is C4-free because the original Heawood graph has girth 6 and contracting one edge can shorten a simple cycle by at most one.

The graph has no induced Near subgraph at all. This was checked by an exact threshold-core algorithm: for each possible exceptional vertex w, repeatedly remove every other vertex of current degree below 3. Any induced Near subgraph with exception w survives every deletion, so the final core decides existence. Every final core has no vertex of degree at least 3.

Full edge list:
(0,11),(0,13),(1,2),(1,7),(1,12),(2,4),(2,9),(2,13),
(3,7),(3,9),(3,10),(4,10),(4,11),(5,9),(5,11),(5,12),
(6,10),(6,12),(6,13).

This graph has power cycles and is not an original counterexample. Therefore the all-power-free condition remains indispensable; the degree/pruning upgrade alone is invalid.

