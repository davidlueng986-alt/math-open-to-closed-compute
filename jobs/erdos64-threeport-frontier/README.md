# Three-port substitution direct closure attack

For a connected simple cubic base graph, substitute a disjoint connected
simple gadget at each vertex. Every gadget has three degree-two ports, all
other degrees three, and no internal power-of-two cycle. Also allow the
singleton with all three ports equal. Join the corresponding external edges.

A simple cycle not confined to one gadget crosses any visited gadget in
exactly two external edges: its boundary has three edges, and crossings of a
cycle have even parity. It therefore projects to a simple cycle of the base.
Conversely every selection of a simple port-to-port path inside each visited
gadget lifts a base cycle to a simple original cycle. The length spectrum of
such a lifted cycle is exactly the external-edge count plus the Minkowski
sum of the selected port spectra. This is an exact finite equivalence.

The census enumerates nonisomorphic connected simple degree sequence
(2,2,2,3,...,3) gadgets at orders 3,5,...,17 using nauty, with full cycle
checks at 4,8,16 as applicable. Its C++ filter and spectra are independently
recomputed in Python for retained gadgets. The fixed base family consists
of ALL connected simple cubic graphs of orders 4,6,8,10. All distinct labelled
spectral types including the singleton are offered. Deduplicating states
with the same order and all three spectra is sound for this feasibility
criterion. The lazy SAT search uses concrete path-length witnesses to
exclude all local choices allowing a forbidden sum, not just the last
exact assignment. Kissat re-proves each final UNSAT CNF and DRAT-trim checks
the proof; CNF/cuts/states retained as artifacts. This is not a general
nonexistence proof: large gadgets and bases outside the domain remain open.
An independently checked expanded graph would be an actual original
counterexample. Timeout or solver report without proof is not a certificate.
