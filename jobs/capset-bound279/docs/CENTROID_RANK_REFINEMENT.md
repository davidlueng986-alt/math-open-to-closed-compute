# CAP066: exact residual-centroid rank refinement

This is an additional necessary constraint on the same codimension-two
count grids. It is not an assumption that the grid relaxation is realizable
by points. All arithmetic in the final certificates is integral.

## Simultaneous centering

Write a seven-dimensional cap as three parallel six-dimensional sections
with sizes A, B, C and six-dimensional point sets S_0, S_1, S_2. An affine
map `(y,x) -> (y,x+t+y*w)` supplies two independent translation parameters.
If a section size n is not divisible by3, its point sum changes by
`n*(t+y*w)`. Therefore any two such section centroids can simultaneously
be set to zero. We choose the first two nonzero sizes modulo3, in the
fixed order A,B,C; if only one size is nonzero modulo3, center that one.

For a six-dimensional projective normal f, the three level counts in a
row are `(a0,a1,a2)`. The evaluation of f on the point sum is

    f(sum S) = a1 + 2*a2 = a1 - a2  (mod3).

A centered row hence satisfies a1=a2 modulo3 for every f. The other
one or two point sums are fixed vectors in F_3^6. They are not independent
choices from one direction to the next.

## One remaining vector

There are364 projective normals in six dimensions. If the remaining
point sum u is zero, all364 normals annihilate it. If u is nonzero,
exactly `(3^5-1)/2=121` normals annihilate it. Thus the extra feature

    J_u(f) = 1[f(u)=0]

has target364 or121, respectively. These two cases are exhaustive.

## Two remaining vectors

Let the remaining point sums be u and v. Add the four features

    J_u, J_v, J_(u+v), J_(u-v).

Their target vectors fall into exactly six cases:

| Relation | Four indicator totals |
|---|---|
| u=v=0 | (364,364,364,364) |
| u=0, v!=0 | (364,121,121,121) |
| v=0, u!=0 | (121,364,121,121) |
| u=-v!=0 | (121,121,364,121) |
| u=v!=0 | (121,121,121,364) |
| u,v linearly independent | (121,121,121,121) |

Over F_3 the four displayed dependent nonzero cases exhaust all possible
one-dimensional spans. In the independent case all four linear
combinations are nonzero. In that case40 normals annihilate both
vectors, also following from the displayed totals: the sum of the four
indicators is1 when `(f(u),f(v))` is nonzero and4 when it is zero, so
`4*121=364+3*40`.

The six cases do not presume anything about the relative positions of
the sections beyond their actual point sums. Their complete coverage
is therefore a valid finite branch split for a global exclusion proof.

## Relation to the eight existing moments

The ordinary feature vector is

    (1,S2_A,S3_A,S2_B,S3_B,S2_C,S3_C,cross_T).

For row size n, its summed targets are

    M2(n)=121*n^2+243*n,
    M3(n)=40*n^3+243*n^2+81*n.

The count target is364 and the cross target is121*A*B*C. Appending the
above indicators gives nine or twelve exact necessary moments. A
nonnegative pointwise integer functional with negative target total
excludes its branch; every branch must be excluded before the parent
profile can be declared impossible.

For target280 and profile(109,108,63), the ordinary eight-moment system
has an exact positive rational witness. The two remaining point sums
are those of the108- and63-point sections. All six twelve-moment branches
have exact exclusion certificates, independently replayed on every
labelled grid in `frontier279/M280/P1_centroids_independent.json`.
This closes a real gap left by the ordinary count-grid relaxation.

## Discovery normalizations and independent replay

Per-grid reflection negates all remaining point-sum evaluations, so it
preserves all zero indicators. The opposite cyclic shifts used when
two rows are uncentered preserve their evaluations modulo3: in that
case both row sizes are divisible by3. Thus the normalizations used in
discovery preserve these added features. Duplicate columns are removed
only after appending all centroid features.

`verify_frontier_centroids.cpp` does not use those normalizations. It
retains all row and level labels, reconstructs the eight moments and
all centroid indicators directly, and checks every allowed grid using
128-bit integer arithmetic. Its strict negative target value and
nonnegative minimum grid value are the evidence; numerical optimizer
status alone is not used as a proof.
