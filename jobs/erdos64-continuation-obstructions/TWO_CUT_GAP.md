# ERDOS-64 nonbipartite two-cut continuation: exact obstruction and remaining theorem

No additional terminal leaf is discharged in this continuation. The original remains OPEN.

## 1. Complete target, with the full degree hypotheses retained

Take two disjoint finite simple graphs A,B with distinct ports a0,a1 in A and b0,b1 in B. Add exactly the two crossing edges a0b0 and a1b1 to obtain J. Assume J is Near in the exact production definition: at least one vertex has degree at least 3, and all except at most one vertex have degree at least 3.

A sufficient all-order theorem for all six remaining nonbipartite low2 leaves is:

> If A and B are power-cycle-free, then there are simple port-to-port paths p in A and q in B such that |p|+|q|+2 is a power of two at least 4.

This is the two-cut subclass of the exact Near conjecture. It is sufficient but stronger than the requested minimal-counterexample exclusion: the latter may additionally exploit all smaller Near competitors. No proof of this theorem is claimed.

The subsequent exact equivalence in CONNECTED_CUT2_EQUIVALENCE.md shows that this standalone target has the full original problem's logical strength, even when both cut sides are required connected. It should not be treated as an easier independent obligation.

For a globally order-minimal bad Near graph, connectedness and the existing one-defect argument eliminate cuts of sizes 0 or 1 and cuts whose crossing edges share an endpoint. For a matching two-edge cut, each crossing simple cycle uses both cut edges, exactly one simple port-to-port path in each side, and no other vertices. Hence the complete crossing spectrum is exactly P_A+P_B+2. The equality, not just containment, follows by concatenation of any two paths in disjoint sides.

## 2. New exact obstruction: all elementary closure spectra can agree without a power cycle

The candidate inference examined was: edge closing, two-edge-path closing, port identification, contraction of one or both crossing edges, and self-copy gluing force enough near-dyadic path lengths that a crossing power cycle follows arithmetically.

That inference is false without additional use of the degree/minimality hypotheses. An exact realizable pair of port spectra is

P_A = {2,3,4},
P_B = {8,13,14,15}.

Then

P_A+P_B = {10,11,12,15,16,17,18,19},

so P_A+P_B+2 contains no power of two. Nevertheless:

| Elementary operation | A witness | B witness / crossing witness |
|---|---:|---:|
| Add an edge between ports | 3+1=4 | 15+1=16 |
| Add a two-edge path between ports | 2+2=4 | 14+2=16 |
| Identify the ports | path length 4 | path length 8 |
| Contract one crossing edge | — | 2+13+1=16 |
| Contract both crossing edges | — | 2+14=16 |
| Join two copies of the same side by two edges | 2+4+2=8 | 15+15+2=32 |

Thus even synchronizing these several surgeries does not resolve the missing intersection. A proof must use information absent from this scalar package.

## 3. Explicit graph realization, verified without a search

A multitheta consists of internally vertex-disjoint paths between common endpoints x,y. Every simple cycle uses exactly two of those paths.

For A, take three x-y arms of lengths 4,1,2. On the length-4 arm take ports at positions 1 and 3 from x. There are exactly three simple port paths, of lengths 2,3,4. Its internal cycle lengths are 3,5,6. A has 6 vertices.

For B, take four x-y arms of lengths 10,11,12,13. On the length-10 arm take ports at positions 1 and 9. Its port paths have lengths 8,13,14,15. Its internal cycle lengths are 21,22,23,23,24,25. B has 44 vertices.

Join the corresponding ports by two edges. The resulting 50-vertex graph is biconnected and has exactly 21 simple cycles: 3 internal to A, 6 internal to B, and 3*4=12 crossing. The complete distinct cycle-length set is

{3,5,6,12,13,14,17,18,19,20,21,22,23,24,25}.

It therefore has no power-of-two cycle.

Crucial scope: its degree counts are 42 vertices of degree 2, six of degree 3, and two of degree 4. It is NOT Near, NOT an original counterexample, and NOT a counterexample to the desired two-port theorem. It falsifies only the proposed spectrum-only deduction after discarding global degree information.

The prescribed construction, full adjacency list, independent simple-path and simple-cycle enumeration, and numerical assertions are in obstruction.py and obstruction.json. This is one explicit falsification test, not a finite census or extrapolation.

## 4. What full minimality adds, and what remains unproved

In a MinimalBad graph, a side of a matching 2-cut which avoids the existing defect cannot have a high-degree port: if one port has original degree >=4, the induced side retains degree >=3 there and has at most one other low vertex, giving a smaller bad Near graph. Therefore both ports on a defect-free side must be cubic in the original graph (degree 2 internally).

For cubic degree type C, both sides consequently have exactly two internal degree-2 ports and all remaining vertices cubic. For degree types S/H, one side has these two ports (with arbitrary higher internal degrees permitted in H); the other carries the original defect as well. These stringent global degree conditions fail in the explicit obstruction above, and are the exact structural resource still missing from the attempted arithmetic argument.

Closing sides individually only gives nonempty dyadic port spectra. It does not identify a common exponent. Contraction strengthens this to sums equal to a power or a power minus one, but the displayed realizable spectra demonstrate that these demands remain compatible with avoidance of power minus two. No rigorously justified conversion of the full degree conditions into the needed collision has been found.

The highest-value continuation is a structural theorem about power-free two-port graphs with all nonport degrees >=3, or a genuine finite original counterexample obtained by satisfying those degree constraints. More scalar shift identities alone cannot complete the proof.

