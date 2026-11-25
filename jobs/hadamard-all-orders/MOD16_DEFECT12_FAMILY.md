# Parametric D12+ shadow model modulo 16

For every \(r\ge1\), let \(t=4r+3\), \(n=4t\), \(u=2r+1\), and \(k=n-12\). There is an exact zero-sum \(D_{12}^{+}\) shadow frame with covariance \(tI\) and row lattice \(D_{12}^{*}\) together with a normalized \(n\times k\) sign matrix satisfying the two augmented Gram congruences from [the order-2396 model](MOD16_DEFECT12.md). The construction has the two Gram identities **exactly** when \(r=1,2,3\), so it gives maximal partial Hadamards of orders 28, 44, and 60 with no sign column appendable.

## Source family and tetrad

Use the Goethals–Seidel matrix \(H\) in array (3) and Theorem 3.2.2 of [Eliahou–Kervaire, *A survey on modular Hadamard matrices*](https://morfismos.cinvestav.mx/sites/default/files/Upload/vol07-n2-2.pdf). Each block is a circulant \(F\), a circulant times reversal \(FR\), or a transposed circulant times reversal \(F^{\mathsf T}R\), with source index \(j-i\), \(-j-i\), or \(j+i\) modulo \(t\), respectively. Matrix entries are indexed \((g,j)\) for block number \(0,\ldots,3\) and within-block coordinate \(0,\ldots,t-1\).

For short sequences \(F,G\) of length \(u\), put
\[
 (a,b,c,d)=([F;\varepsilon;-F^\#],
 [F;\varepsilon;-G^\#],
 [G;\varepsilon;-F^\#],
 [G;-\varepsilon;-G^\#]),\qquad
 \varepsilon=(-1)^{r-1}.
\]
Here \(\#\) reverses the entries after multiplying the entry at position \(j\) by \((-1)^j\). For even \(r\), \(F=[1^{2r+1}]\) and \(G=[(-1)^{r+1};1^r]\). For odd \(r\),
\[
 F=[1^{r-1};-1,1,1;(-1,1)^{(r-1)/2}],\quad
 G=[(-1)^{r-1};1,-1,1;(-1,1)^{(r-1)/2}].
\]
Thus \(F_jG_j=-1\) exactly for \(0\le j\le r\).

Take \(I=((1,u),(1,u+1),(3,u),(3,u+1))\). For \(\Delta f(j)=f_j f_{j+1}\), the product of these four rows in column blocks \(0,1,2,3\) is, respectively,
\[
 \Delta(bd)(-j-u-1),\quad \Delta(ac)(j+u),\quad
 \Delta(bd)(j+u),\quad \Delta(ac)(j+u).
\]
For example, block 1 combines two consecutive values of \(a\) starting at \(j-u-1\) and two consecutive values of \(c\) starting at \(j+u\). These starting positions are equal modulo \(t=2u+1\). The signs of the Goethals–Seidel array cancel in each adjacent row pair. The product \(ac\) is negative on \(\{0,\ldots,r\}\) and \(bd\) adds the single negative index \(u\). Consequently the negative positions are the following \(J\).
\[
\begin{array}{c|l}
\text{column block}&\text{within-block positions}\\\hline
0&0,1,r+1,u+1\\
1&u,3r+2\\
2&0,u,3r+2,t-1\\
3&u,3r+2
\end{array}
\]

The four rows in \(I\) and the thirteen columns \(J\cup\{(0,r)\}\) are separately pairwise exactly orthogonal when \(r\ge2\). Indeed, cross-block Gram entries vanish in the Goethals–Seidel array, and the only nonzero within-block off-diagonal entries have even least circular distance at most \(r-2\). This follows from the cited aperiodic coefficient formula \(32(\lfloor r/2\rfloor-i)\) at shifts \(2i\), which vanishes at \(i=\lfloor r/2\rfloor\), and periodization. Within \(I\), distinct selected rows of a block have distance 1. Within \(J\cup\{(0,r)\}\), each distance is 1 or at least \(r-1\). At \(r=1\), use \((0,3)\) instead of \((0,r)\) as normalizing column. At \(r=1,2,3\) the entire source Gram is exact by the same coefficient formula.

## Reflect and establish the lattice

Normalize the indicated column by row signs and apply \(J_4/2-I_4\) to \(I\). Since the normalizing column lies outside \(J\), the tetrad product is unchanged by normalization. Kept columns remain signs and removed columns acquire one spike \(\pm2\) on the tetrad. Write the resulting matrices as \(A,R\), with \(V=R/2\). Exact panel orthogonality gives \(R^{\mathsf T}R=nI\) and zero column sums of \(R\). Exact orthogonality of \(I\) gives norm 12 for each row of \(R\), so the four rows in \(I\) have precisely three spikes each on pairwise disjoint supports. Remaining rows of \(R\) are sign rows.

The congruence \(AA^{\mathsf T}+RR^{\mathsf T}\equiv nI\bmod16\) follows as in [the fixed-order proof](MOD16_DEFECT12.md): the original row error is \(32E\) with \(E\) symmetric integral of zero diagonal. Outside the tetrad no division occurs. The cross block divides by 2, and the tetrad block divides by 4 but its numerator sum is even modulo 2. This congruence also forces all half-shadow sign rows of \(R\) to have the same row product. For a fixed sparse row, every scalar product with a sign row in \(R\) is 2 modulo 4, so each corresponding row of \(A\) has opposite parity to the sparse row. Thus any two sign rows give scalar product 0 modulo 4 in \(R\), meaning that their Hamming distance is even. If necessary, negate one column of \(R\) so that every such sign row has an odd number of negative signs and hence coordinate sum 2 modulo 4. For the four sparse rows this congruence is automatic. The rows of \(V\) now lie in the two types of the single shadow coset \(D_{12}^{*}\setminus D_{12}^{+}\). The row product condition for \(A\) follows after choosing a sparse first row and normalizing its column signs.

Let \(L\) be the row lattice of \(V\). It satisfies \(tD_{12}\subseteq L\), by the exact frame identity. The sparse/half types generate \(D_{12}^{*}/D_{12}\), giving \(L+D_{12}=D_{12}^{*}\). Thus the index \([D_{12}^{*}:L]\) is odd. The minors below are powers of two in doubled coordinates and give an index dividing 4 or 8, so \(L=D_{12}^{*}\) and the even-total combinations generate \(D_{12}^{+}\).

For an integral basis \(B\) of \(D_{12}^{+}\), the cross term \(A^{\mathsf T}R\equiv0\bmod32\) gives \(A^{\mathsf T}RB\equiv0\bmod16\). The other column block is exact, \((RB)^{\mathsf T}(RB)=nB^{\mathsf T}B\). This establishes both Gram congruences. If \(r=1,2,3\), both identities are exact by orthogonality of the source and reflection. The unit-free \(D_{12}^{+}\) then rules out additional sign columns by [the exact obstruction](DEFECT12_EXACT.md).

## Minor certificates

For even \(r\ge4\), use block-0 rows
\[
 (0,1,2,3,r+2,r+3,u+1,u+2,3r+3,3r+4)
\]
and block-1 rows \(0,1\). In the order of \(J\) above, the 12 row words of the source sign matrix in hexadecimal, with least significant bit the first column and bit 1 a negative sign, are
\[
 \mathtt{928,429,4f2,6b1,876,311,837,d7a,e1c,db0,fb8,402}.
\]
Their determinant has absolute value \(8192\).

For odd \(r\ge7\), use block-0 rows
\[
 (0,1,4,3,u+2,r+2,r,r+5,u+3,r+1,3r+3,3r+4).
\]
Their words are
\[
 \mathtt{928,0b1,4f2,229,65c,a35,268,113,285,6f0,3a0,969}
\]
and determinant has absolute value \(16384\).

The row words above can be verified uniformly by affine inequalities. For each entry, reduce the source argument \(j-i\), \(-j-i\), or \(j+i\) modulo \(4r+3\) using the quotient at the stated lower endpoint \(r=4\) or \(r=7\). The remaining index stays in range because both affine differences from the endpoints have nonnegative slopes and nonnegative values at the lower endpoint. Apply the same test to the relevant constant-sign or alternating-sign interval of \(F,G\), their sharps, and the middle entry. Alternating sign is constant for the fixed parity of \(r\). The [affine certificate](defect12_mod16_family.py) performs these exact affine checks and determinant evaluations. None of these rows lies in the tetrad, so the reflection does not change them. Row and residual column signs preserve the absolute determinant.

The finite cases below use global zero-based row indices and give minor absolute values in the reflected matrix.

| \(r\) | \(n\) | Minor rows | Absolute determinant |
|---|---:|---|---:|
| 1 | 28 | \(0,1,2,3,4,5,6,7,8,9,10,12\) | 8192 |
| 2 | 44 | \(0,1,2,3,4,5,6,7,9,10,11,12\) | 8192 |
| 3 | 60 | \(0,1,2,3,4,5,7,9,10,11,12,13\) | 16384 |
| 5 | 92 | \(0,1,4,3,13,7,5,10,14,6,18,19\) | 16384 |

There is no remaining minor gap for \(r\ge1\). The [affine certificate](defect12_mod16_family.py) confirms the symbolic minor entries for the infinite cases and the actual minors and source Gram for the small exact cases. The source case \(r=0\) has \(n=12\) and no kept columns, so is outside the family.
