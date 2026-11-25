# New all-order structural exclusion: bipartite deficit 5/6

**Original remains OPEN.** No finite vertex bound is assumed. Extend the
2026-11-24 codimension-two safe-descent theorem (D<=4) for a finite simple
bipartite subcubic graph K with at least one cubic vertex. Put
D(K)=sum_v(3-deg(v)). Assume K is power-free.

**Theorem.** If D(K)<=6, K is not K1,3, and K does not have a balanced
bipartition with exactly three degree-two vertices on EACH side and all
other vertices cubic, then K contains a genuine uniform 2-, 4-, or 8-subdivision of a smaller simple near-cubic graph (all degrees 3
except possibly one degree 2, with at least one cubic vertex).
In particular this includes EVERY K with D<=5 and a cubic vertex.

## Proof (all graph orders)

Let p,q be the sizes of two bipartition sides X,Y; dX,dY their total
deficits, tX,tY their numbers of deficient vertices. Degree equality
is 3p+dY=3q+dX. Since dX+dY<=6 and tX<=dX,tY<=dY,
at least one orientation satisfies q-p+tX<=2, except precisely the
balanced six degree-two port case stated above. Directly: for
p=q, either side with <=2 deficient vertices works unless both have
three degree-two ports. For p=q+1, choose the smaller side as branches
because its deficit <=1; for p=q+2, the smaller side has deficit zero.
Negative differences are symmetric. This is formally checked by
choose_orientation and five_deficit_orientation.

Use that orientation. Its ordinary X columns are degree-three
vertices, with cardinality p0=p-tX. There is at least one such
column: in the balanced case, if p0=0, then p=q<=2, hence no cubic
vertex anywhere (the exceptional balanced tX=3 case was removed or
we choose the other orientation); in the unbalanced orientation
chosen as described, if p0=0 the smaller side has size <=1 and
deficit >=1, hence no cubic vertex anywhere. For clarity, choose the
orientation in this explicit manner, not just an arbitrary witness
of the inequality.

Let M be the F2 incidence map from these columns to Y. If there
is a nonzero kernel, or a unit syndrome, use the earlier exact
pairing construction: delete the single selected incidence at the
unit row, if needed, and suppress the paired Y midpoints. All
branches have degree three except at most one degree two. Distinct
midpoints cannot give duplicate shadow edges (C4-free). Because
the sides are disjoint and subcubic, the subdivision is genuine.
There is at least one cubic vertex (a nonempty simple graph in
which all but at most one vertex have degree3 cannot consist only
of that exceptional vertex of degree2).

Otherwise M is injective and the quotient dimension d=q-p0<=2.
Every standard basis row has a nonzero quotient label. Each
ordinary column has three such labels summing to zero; hence d=2,
with three nonzero labels A,B,C, each ordinary column seeing one
of each. If a degree-two X port has equal neighbor labels, its
column lies in the image of M; add the port to the selected
ordinary support and pair as before. This gives one degree-two
branch, all others cubic. The support on the ordinary columns is
nonempty because the port's incidence column is nonzero.

Otherwise every degree-two X port has two distinct labels. For
each pair i,j in {A,B,C}, build a shadow on those Y labels using
one pair edge for each ordinary X vertex, and also an edge for
each degree-two X port whose two labels are exactly i,j. Ignore
degree-one and degree-zero X vertices. Each shadow is simple
bipartite subcubic, and its edges are genuine length-two
subdivisions in K. Every original Y degree deficit is counted
twice across the three shadows. Each degree-two distinct-label
X port contributes one lost incidence in two shadows. Each
degree-one X port contributes one lost incidence in two shadows.
Degree-zero ports contribute zero. Thus
  sum D(H_ij) = 2(dY + #degree1 X + #degree2 X)
              <= 2(dY+tX) <=12.
Some H has D<=4 by pair_budget.

We still need a cubic vertex in H. If p0>=2, every pair shadow
contains >=2 DISTINCT edges by C4-freeness of K. If it had maximum
degree<=2, its degree sum and D<=4 give n<=4; because it is
bipartite, n<=3 with >=2 edges gives e<=n-1 and D>4.
The only remaining case n=4,e=4 is C4, lifting to C8 in K.
The arithmetic is checked by no_cubic_budget.
If p0=1, q-p0<=2 and the single ordinary X vertex has three
neighbors, so q=3. Every other X vertex has degree<=1, since
two neighbors would give a C4 with the ordinary vertex.
Consequently D>=p+5, and D<=6 forces p=1, giving exactly K1,3,
which was excluded. Hence H contains a cubic vertex.
Apply the prior D<=4 theorem to H: all its cycles lift at double
length into K, so H is power-free. H has a genuine 2- or
4-subdivision of a smaller near-cubic graph. Compose with the
first length-two expansion to obtain length 4 or 8 in K.

## Global consequence

In a minimum-order power-free near counterexample, there is NO
bipartite subcubic subgraph with a cubic vertex and total deficit
<=5, of ANY order. For deficit6, only the star and the balanced
six-port pattern remain possible. This extends the existing
deficit4 theorem. No novelty claim; earlier source is
Ducoffe-Dumitru arXiv:2609.28594 and the project's codim2 proof.

## Attack on the one remaining six-port pattern

For balanced six degree-two ports, if the ordinary incidence
map has neither kernel nor unit syndrome and no equal-label
degree-two port, its quotient dimension is 3. Label each of
the three deficient Y vertices by its nonzero quotient label;
label each of the three degree-two X ports by the sum of its
two distinct neighbor labels. This yields six nonzero vectors
in F2^3, counting multiplicity.

For any nonzero character ell, select Y rows with ell(label)=1.
Each ordinary X row pairs 0 or 2 selected neighbors; each
degree-two X port pairs two, omits one, or does nothing. The
total deficit of the resulting collision-free shadow equals
the Hamming weight of ell on this multiset of six labels.
Every nonzero label is selected by four of the seven characters,
so the sum of the seven deficits is 24; some is <=3.

If none has deficit <=2, all weights are in {3,4,5,6}. Counting
pairs of selected labels over characters gives 30+2d, where d
is the number of equal unordered label pairs: distinct labels
are simultaneously selected by exactly two characters, equal
ones by four. six_port_moments proves d=0 and the only possible
weight distribution is four 3s and three 4s. Thus either a
shadow has deficit <=2 OR the six labels are exactly six of
the seven nonzero vectors. This is an exact new structural
dichotomy, not a proof of the exceptional case: the shadow may
be nonbipartite and may have multiple deficient vertices.
Do not conflate <=2 deficit with the near-degree condition.

Lean scope: this file verifies the universal arithmetic
orientation/deficit/moment constraints. The graph construction
and F2 quotient geometry here remain ordinary mathematical proof;
PairedShadow.lean independently attacks its graph-level component.
