# CAP066: completion of (43,43,h) when h >= 22

## Theorem

Let three parallel five-dimensional sections of a six-dimensional cap
over F_3 have sizes 43, 43 and h. If **h >= 22**, then **h = 22** and
the cap is contained in a 112-point cap.

Thus (22,43,43) is a sufficient completion criterion for108-caps,
while (23,43,43) is impossible for109-caps. This argument does not
import any inequality from the proof of the110-cap Theorem3.9.

## Imported classification facts

We use affine uniqueness of the45-cap and Thackeray's
<https://arxiv.org/pdf/2206.09804>:

- Theorem2.1: every43-cap completes45; a42-cap either completes45
  or is the exceptional Delta686.
- Lemmas2.2 and3.2: two45-caps admit a common(18,9,18) direction
  with18-sections of type882A2; the45-cap symmetry group is
  transitive on directions of this type.
- Lemma2.3: restoring at most two deleted points of an882A2 cannot
  give a different18-cap without a9-point hyperplane.
- Table1 and the Delta686 facts in Proposition3.8's proof:
  its18-sections in profiles(18,18,6) and(18,17,7) have types963B
  and981C, respectively, and hence are not882A2.

These are external classification inputs, not new computations claimed
here. Their roles are isolated from the new finite verification.

## 1. A cross-section of size at least42 is forced

Complete the two outer43-caps to45-caps A and B. By Lemma3.2 choose
coordinates(y,s,u), with y indexing the original three sections and
u in F_3^4, so their completed s-section counts are both(18,9,18)
and all four completed18-sections are882A2 caps. The nine counts
of the original cap have the form

\[
\begin{pmatrix}
18-\alpha_+ & a & 18-\beta_+\\
9-\alpha_0 & b & 9-\beta_0\\
18-\alpha_- & c & 18-\beta_-
\end{pmatrix},\qquad
\alpha_++\alpha_0+\alpha_-=\beta_++\beta_0+\beta_-=2.
\]

All deletion numbers are nonnegative integers, every corner has at
least16points, and h=a+b+c. Put

\[
D=\alpha_++\alpha_-+\beta_++\beta_-=4-\alpha_0-\beta_0\le4.
\]

Consider the top row, bottom row, and two diagonals through b.
Each is a five-dimensional affine section. If all four had at most41
points, then

\[
\begin{aligned}
a&\le5+\alpha_++\beta_+,\\
c&\le5+\alpha_-+\beta_-,\\
b&\le5+\min(\alpha_++\beta_-,\alpha_-+\beta_+).
\end{aligned}
\]

The two arguments of the minimum sum to D, so

\[
h\le15+D+\lfloor D/2\rfloor\le21,
\]

contrary to h>=22. Therefore at least one of these four cross-sections
has at least42points. Middle-level deletions are explicitly included;
they decrease D and strengthen this inequality.

## 2. The large cross-section completes45

Its two outer four-dimensional parts have between16 and18points,
each contained in an882A2. If its size is at least43, Theorem2.1
completes it immediately.

If it has42points, it cannot be Delta686. The only Delta686 profiles
with two entries at least16 are(20,16,6),(18,18,6),(18,17,7).
The first requires an outer part of size20, impossible here. In either
of the other profiles an outer part has size18 and is exactly an882A2,
contradicting the Delta686 section types stated above.

Consequently the cross-section completes45. Both outer parts exceed15,
so its completed profile must be(18,18,9), not(15,15,15). Each restored
18-cap agrees with the original corner882A2 on at least16points.
Every18-section of a completed45-cap is either882A1 or882A2, and both
types have no9-point three-dimensional section. Lemma2.3 therefore
forces it to equal the original882A2: otherwise replacing at most two
points of that882A2 would give a different18-cap without a9-point
section, contrary to the lemma.
The two completed corner18-caps are therefore partners in a45-cap.

## 3. Exhaustive parameterization: rows and diagonals

Fix the first completed45-cap as

\[
A=(\{1\}\times K)\cup(\{2\}\times L)\cup(\{0\}\times N),
\qquad |K|=|L|=18,\quad |N|=9,
\]

with K,L of type882A2. The coordinates supplied to the checker have
K containing0 and the four coordinate basis vectors.

Let G be the affine automorphism group of K. Exhausting every ordered
affine frame gives16maps. A separate frame search gives16 affine
isomorphisms K->L; choose one P. The checker also verifies8 affine
symmetries of A reversing its two18-levels.

Every45-cap whose level1 section is K is an image of A under

\[
T_{g,v}(s,u)=(s,g(u)+(s-1)v),\qquad g\in G,\quad v\in F_3^4.
\]

Completeness follows from45-cap affine uniqueness, transitivity of
882A2 directions, and the verified orientation reversal. Once the
level coordinate and orientation are fixed, restriction to level1
is g, and the remaining affine freedom is precisely v. The1,296maps
give **162 distinct fixed-K extensions**, denoted by E.

Likewise all18-caps partnering K are g(L)+v: **162 distinct partners**.
For each choose the affine map Q=translation(v) composed with g and P,
so Q(K)=g(L)+v.

After reversing s if necessary by a symmetry of the fixed A, the large
cross-section joins K either to level1 of B(horizontal) or level2 of B
(diagonal). Enumerate both:

\[
B=\{(s,Q(u)):(s,u)\in E\},\qquad
B=\{(-s,Q(u)):(s,u)\in E\}.
\]

There are **26,244 distinct B in each orientation**. In the diagonal
case reversing the level coordinate in B is part of the parameterization;
it is not presumed to be a symmetry of the whole six-dimensional cap.
This covers every completed pair forced by step2. The later bound
allows arbitrary two deletions from each side, including middle points.

## 4. Weighted representation capacity

For each completed pair define

\[
r(z)=\#\{(x,y)\in A\times B:x+y=z\},\qquad
T=\{z:r(z)\le4\}.
\]

Set d_A(x)=#{y in B:x+y in T} and d_B(y)=#{x in A:x+y in T}.
Let R be the sum of the two largest A-degrees and two largest B-degrees.
Deleting two points per side can destroy at most R representations with
sum in T. All resulting holes belong to T, because representations of
one sum form a matching and at most four endpoints are deleted. For
the hole set H, necessarily

\[
\sum_{z\in H}r(z)\le R.
\]

Counting a representation twice when both endpoints are deleted only
increases this upper estimate. Sorting the values r(z), z in T, gives
an exact integer upper bound on |H|: take the largest number of cheapest
values whose sum is at most R. Original zero-cost holes are included.

| Partner orientation | Completed pairs | Point-reflection pairs | Hole bound for every other pair |
|---|---:|---:|---:|
| Horizontal | 26,244 | 81 | 10 |
| Diagonal | 26,244 | 0 | 9 |

The checker identifies reflection directly by a sum z_0 with r(z_0)=45,
which forces B=z_0-A, and verifies that point-set equality. It does
not infer reflection from a histogram alone.

Since h>=22, every nonreflection pair is impossible. For a reflection
pair the convolution has22zeros,220values of9 and one value45. Four
deletions cannot create a new hole. The original22holes form a cap;
restoring the four outer points and all missing hole points yields a
112-cap. Thus h=22 and completion follows.

## Verification

`verify_cross_section_capacity.cpp` starts from the normalized45point
set alone, checks its cap property, reconstructs all affine maps by
complete frame enumeration, and checks both partner families and all
weighted representation bounds. It identifies the selected882A2
direction by checking all55(18,9,18)directions:45have its855-cube
property and10do not; both chosen18-sections have that property.
Cube checks explicitly enumerate affine cube frames. No optimizer is
used.

`prove_cross_section_capacity.py` independently replays the exact
convolution/capacity calculations in pure Python. The reflection-hole
cap property is independently checked by `verify_reflection_completion.py`.

The(23,43,43) prohibition applies to every109-cap. The(22,43,43)
completion criterion becomes a seven-dimensional exclusion only where
completed108-sections have separately been excluded.
