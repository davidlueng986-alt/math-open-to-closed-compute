# CAP066: a completion theorem for the profiles (44,43,c), c >= 20

## Result and scope

**Theorem.** Let a cap in the six-dimensional affine space over F_3 have
three parallel five-dimensional sections of sizes 44, 43 and c. If c >= 20,
then c <= 22 and the entire cap is contained in a 112-point cap.

Consequently the profiles **(22,43,44), (21,43,44), and (20,43,44)** are
sufficient completion criteria for caps of sizes 109, 108 and 107,
respectively. The profiles (c,43,44) with c >= 23 are impossible.

This is a computer-assisted theorem with explicitly stated external
classification inputs. It does not by itself exclude all 281-point
seven-dimensional caps or establish a global upper bound of 280.

## External inputs

1. All 45-point caps in F_3^5 are affinely equivalent. This is the already
   imported classification of Edel, Ferret, Landjev and Storme (2002).
2. Every 43- or 44-point cap in F_3^5 extends to a 45-point cap:
   Thackeray, *The cap set problem: up to dimension 7*, Theorem 2.1.
3. For two complete 45-point caps A,B, the proof of Proposition 3.5 in
   that paper gives the following exhaustive alternatives. They are
   translates; they are point reflections; or the number n_2 of sums
   with representation count at most two is at most 14. More precisely,
   the nontranslation, nonreflection alternatives have (n_0,n_2)=(6,6),
   (2,14), or n_0 <= 5 and n_2 <= 13.

Primary source: <https://arxiv.org/pdf/2206.09804>, Theorem 2.1 and
Proposition 3.5 with its proof, pages 1 and 8–9 of the paper.
The classification computation underlying these external statements has
not been rerun here. The new finite graph lemma below is verified here
in two independent implementations.

## The new five-hole lemma

Let A be a 45-point cap in F_3^5, let B be any subset of F_3^5, and choose
a in A and distinct b_1,b_2 in B. Put

\[
A'=A\setminus\{a\},\qquad B'=B\setminus\{b_1,b_2\}.
\]

For z in F_3^5 write r(z) for the number of representations z=x+y with
x in A and y in B. Then

\[
\#\{z\notin A'+B':r(z)\ge3\}\le5.
\]

### Reduction to an independent-set problem

Translate B by -b_1 and each sum z by -b_1. Thus b_1=0 and b_2=d != 0,
with A and a unchanged. Representations of one sum form a matching
between A and B. Deleting a,0,d can destroy at most three representations.
Therefore a hole with r(z) >= 3 must have r(z)=3, and all three deletions
must destroy different representations. In particular,

\[
z\in V=(A\cap(A+d))\setminus\{a,a+d\},\qquad z-a\in B.
\]

For distinct z,w in V place an edge between them if

\[
a+z-w\in A\quad\hbox{or}\quad a+w-z\in A.
\]

Any set H of these high-representation holes must be independent in this
graph. Indeed, if a+z-w is in A, then

\[
z=(a+z-w)+(w-a)
\]

is a surviving representation: the first endpoint differs from a because
z != w; the second belongs to B and differs from 0,d because w is in V.
The reverse edge condition is handled by interchanging z and w.

### Exact finite verification

For the standard 45-point cap supplied in `cap45.json`, all 242 nonzero
differences d and all 45 choices of a are checked. Every overlap has
size zero or nine, so each graph has at most nine vertices.

| Independence number | Number of (a,d) cases |
|---:|---:|
| 0 | 990 |
| 4 | 5,400 |
| 5 | 4,500 |
| **Total** | **10,890** |

`prove_three_deletion.py` computes independence numbers by a recurrence
over all subsets. `verify_three_deletion.cpp` independently uses
base-three encoded points, reconstructs each graph, and inspects the
edges of every subset directly. In particular it rejects every candidate
independent six-subset. Both checks pass without any optimization solver.

The construction is affine invariant: under x -> Mx+t on A, a and graph
vertices, and d -> Md, the condition a+z-w in A is preserved. The affine
uniqueness of 45-caps therefore transfers the finite bound to every A.
This proves the five-hole lemma. Notice that B need not itself be a cap
for this lemma.

## Completion proof

Complete the sections of sizes 44 and 43 to two 45-point caps A and B.
The original sections are A' and B', obtained by one and two deletions.
The third section is contained, up to negation, in the holes of A'+B'.

If A and B are neither translates nor point reflections, the external
classification gives n_2 <= 14. At most n_2 holes have original
representation count at most two; the five-hole lemma bounds all other
holes. Hence

\[
|F_3^5\setminus(A'+B')|\le14+5=19,
\]

contradicting c >= 20.

If B is a translate of A, the sum representation distribution is one
representation at 45 sums and ten at each of the other 198 sums.
The singly represented sums use matching pairs (x,x), up to translation.
Three endpoint deletions open at most three such holes, while sums with
ten representations cannot become holes. Again c >= 20 is impossible.

It follows that B is a point reflection of A. Its convolution distribution
has 22 zeros, 220 values of nine, and one value of 45. Three deletions
cannot open a new hole. The original 22 holes form a cap; restoring the
three deleted outer points and all missing points of this 22-cap yields
a cap of size 45+45+22=112. This proves both c <= 22 and completion.

The translation and reflection distributions, the cap property of the
22 holes, and the resulting 112-cap are all checked directly by
`verify_reflection_completion.py`. It also supplies nonvacuous examples
with the three new profiles.

## Consequence for CAP066's seven-dimensional search

CAP065 already excludes every 109-point section that completes to a
112-point cap in a hypothetical 281-point cap. Therefore the new
(22,43,44) criterion is a legitimate additional forbidden internal
profile for every remaining 109-point section. The 108-point and
107-point criteria only yield a seven-dimensional exclusion when the
corresponding completed-section context has separately been proved;
they must not be promoted to unconditional bans on all such sections.
