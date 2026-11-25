# Arbitrary four-port assembly exclusion

**Status:** complete ordinary mathematical argument for an entire unbounded
construction family; independently checked by the defect-core agent. Not yet a
Lean theorem, and not an exclusion of an entire existing Closure DAG leaf.
The original Erdős–Gyárfás conjecture remains unresolved.

## Theorem

Let P be the graph on {0,1,2,3,4,5} with edges

    01, 02, 14, 23, 34, 35, 45.

Take any nonempty finite collection of disjoint copies of P. The four degree-two
vertices 0,1,2,5 of every copy are ports. Pair all ports arbitrarily, and join
each pair by an edge. If the resulting graph is simple and every port gains
one new incident edge, the resulting cubic graph has a simple cycle of length
2^k for some k >= 2.

There is no ring, orientation, global port-color consistency, connectivity, or
number-of-blocks assumption.

## Proof

Partition the ports of each copy into R={0,5} and B={1,2}. Direct inspection of
simple paths in P gives the following exact spectra.

| Port pair | All simple path lengths |
|---|---|
| 0--1, 0--2 | A={1,4,5} |
| 5--1, 5--2 | B={2,3,4,5} |
| 0--5 | {3,4} |
| 1--2 | {2,3,4} |

The script `audit.py` separately enumerates every simple
path in this six-vertex graph and saves a witness for each listed length.

First handle exceptional joins. A join within one block either duplicates the
already existing edge 01 or 02, contrary to the construction assumptions, or
creates a C4. For example, the other four possible joins are 05,12,15,25,
and existing paths of length three between their endpoints are respectively
0-1-4-5, 1-4-3-2, 1-4-3-5, and 2-3-4-5.

Now split each block into two auxiliary vertices R_i and B_i and add an edge
R_i B_i. These edges form a spanning perfect matching M. Each original joining
edge becomes an auxiliary edge between the classes containing its two ports.
The joining edges form a spanning 2-regular multigraph F on the auxiliary
vertices. A parallel pair in F uses two different ports at each of two blocks.
The within-block path spectra give cycle-length intervals [8,10], [7,10], or
[6,10], according as the two endpoint classes are R/R, R/B, or B/B. Each
contains 8. We may therefore assume that F is simple. It has no loops, by the
preceding intrablock check, and it is edge-disjoint from M.

Use the Grossman--Häggkvist alternating-cycle theorem: if a finite graph's edges
are partitioned into two nontrivial spanning regular subgraphs, it has a simple
cycle whose edges alternate between the two parts. Apply it to M (1-regular)
and F (2-regular). No connectivity hypothesis is needed in this version.

The alternating cycle traverses the two auxiliary vertices of each visited
block consecutively along its M edge. Thus it projects to a cycle through m
distinct blocks, using one R port and one B port in each, where m >= 2. The
value m need not be even. A two-block projected cycle is allowed and uses two
distinct joins. It lifts to an ordinary simple cycle in the original graph.

Suppose q of the m local traversals use port 5. Their internal path spectra
are B, and the other m-q spectra are A. Choices in different blocks are
independent, and adding the m joining edges gives all lengths in

    m + (m-q) A + q B,

where addition is Minkowski sum of sets of integers.

If q >= 1, this is exactly [2m+q,6m]. Indeed A+B=[3,10], adjoining another A
to an interval of width at least two leaves an interval, and B is itself an
interval. The case q=m is immediate. Since q<=m, the upper endpoint 6m is at
least twice the lower endpoint. This interval therefore contains a power of
two at least four.

If q=0, the achievable lengths are

    2m + 3a + 4b,    a,b>=0, a+b<=m.

They include 2m and every even integer in [2m+4,6m]. To see the latter, put
D=L-2m. If D is divisible by four, take a=0,b=D/4. Otherwise D is even and
D>=6; take a=2,b=(D-6)/4. In the latter case D<=4m-2 gives a+b<=m.

Let P_0 be the least power of two at least 2m. It lies below 4m. The preceding
achievable set contains P_0 unless P_0=2m+2. In that exceptional case it
contains 2P_0=4m+4, because m>=2 gives 4m+4<=6m. This completes the proof.

## Literature dependency

The precise alternating-cycle result used above is the regular-subgraphs
corollary in:

J. W. Grossman and R. Häggkvist, *Alternating cycles in edge-partitioned
graphs*, Journal of Combinatorial Theory, Series B **34** (1983), 77--81.
DOI: https://doi.org/10.1016/0095-8956(83)90008-4 .

The primary article's abstract explicitly states that the connectivity
assumption can be omitted when both subgraphs are regular. An accessible exact
statement is Corollary 3.6, p. 6, in J. Bang-Jensen and G. Gutin,
*Alternating cycles and paths in edge-coloured multigraphs: a survey*:
https://www.cs.rhul.ac.uk/~gutin/paperstsp/alt.pdf .

The current package does not contain a Lean proof of this theorem; it must not
be introduced as a new axiom in a kernel-verified closure claim.

## Exact obstruction to a universal extension

An alternating cycle in an arbitrary cubic graph need not have dyadic length,
even when every matching-alternating cycle is considered and the graph is
C4-free and bipartite.

For s>=3, define vertices R_(i,j), B_(i,j), with i modulo 3 and j modulo s.
Use the matching M={R_(i,j) B_(i,j)} and other edges

    R_(i,j) B_(i+1,j),    R_(i,j) B_(i+1,j+1).

This graph is simple and cubic. An M-alternating cycle projects to a directed
cycle on the labels (i,j) in which every arc increases i by one modulo three.
Every M-alternating cycle consequently has length divisible by six, so none
has length a power of two. This divisibility argument is valid for every s.

For s=3 the graph has 18 vertices and is C4-free: a cycle with no M edge lies
in one of three F-components C6, while a C4 with two M edges is alternating
and would project to a directed two-cycle, which is impossible. A C4 with one
M edge would require an F-path from R_(i,j) to B_(i,j); its endpoints belong
to different F-components (the component of R_i contains B_(i+1)), so this
is impossible. Three or four M edges on a C4 are impossible because M is a
matching. The saved exact calculation confirms
that its M-alternating cycle lengths are exactly 6,12,18 and supplies actual
C8 and C16 witnesses in the full graph. This is a counterexample to a route
claim, not a counterexample to Erdős--Gyárfás.

The gap in a universal block method is therefore the existence of sufficiently
flexible local path spectra along a forced compatible cycle. The matching
theorem settles only the cycle's existence. Furthermore, a finite catalogue
of cyclic blocks of bounded order cannot cover cubic graphs of arbitrarily
large girth. Replacing the remaining DAG leaves by the assertion that such a
catalogue is unavoidable would introduce a false bridge.

## Verification record

`python dag_continuation/audit.py` completed successfully.
It checks exact six-vertex path spectra, all mixed sumsets for 2<=m<=64, the
explicit all-A dyadic construction for 2<=m<=4096, and the displayed cubic
graph for s=3. These finite checks support transcription and boundary
cases; the all-order proof is the argument above, not the computation.
