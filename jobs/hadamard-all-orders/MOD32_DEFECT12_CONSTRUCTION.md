# A defect-12 model modulo 32 for \(t\equiv3\pmod{16}\)

For every \(t=16k+3\), \(k\ge1\), there is an exact zero-sum \(D_{12}^{+}\) shadow frame \(V\) of size \(n\times12\), where \(n=4t\), with \(V^{\mathsf T}V=tI_{12}\) and row lattice \(D_{12}^{*}\). There is a normalized sign matrix \(A\) of size \(n\times(n-12)\). For an integral basis \(B\) of \(D_{12}^{+}\) in columns, put \(P=[A\ 2VB]\) and \(D=\operatorname{diag}(I_{n-12},B^{\mathsf T}B)\). Then
\[
 P^{\mathsf T}P\equiv nD\pmod{32},\qquad PD^{-1}P^{\mathsf T}\equiv nI\pmod{32}.
\]
The first member at \(n=76\) satisfies both identities exactly and gives a maximal \(76\times64\) partial Hadamard. A separate certificate below gives the modulo-32 model at \(n=156\). The family does not include \(t=599\), which is \(7\) modulo 16. See [the separate obstruction at order 2396](MOD32_DEFECT12.md).

## Source and exact panel

Use the 64-modular Goethals–Seidel matrix \(H\) from [Eliahou, *An update on modular Hadamard matrices*, Construction 6.1](https://doi.org/10.1007/s10801-026-01544-5). Here is the run-length data from the [author's lecture slides](https://us.ticmeet.com/assets/archivos/d6f1d9b8-d39f-4888-925a-7eb81c4905cc/Eliahou.pdf). Each list starts positive and alternates signs at each run.
\[
 \begin{aligned}
 q&=(8k+1,2,8k-1,1),\\
 s&=(4)^k(2,1,1)^k(2,1,2)(1,1,2)^{k-1}(1,3)(4)^{k-1}(1,1).
 \end{aligned}
\]
Let \(\tau\) equal \(+1\) on the first \(8k+2\) positions and \(-1\) on the rest. The four sign sequences are \((a,b,c,d)=(s,s\tau,sq,sq\tau)\). Index both row and column blocks by \(0,1,2,3\), and within each block use zero-based indices modulo \(t\). Use the circulants with source index \(j-i\) and reversal \(j\mapsto-j\).

Put \(u=4k\) and take the tetrad consisting of the rows at offsets \(u,-u\) in blocks 2 and 3. Since \(ab=cd=\tau\) pointwise, its four-row product on column blocks 1, 2 and 3 at coordinate \(j\) is \(\tau(j-u)\tau(j+u)\). On block 0 the same product is evaluated at \(-j\). The product is \(+1\) on the following three positions in each block.
\[
 \begin{array}{c|l}
 \text{block}&\text{within-block positions}\\\hline
 0&u+1,3u+2,3u+3\\
 1,2,3&u,u+1,3u+2
 \end{array}
\]
In fact the two \(\tau\) arguments differ by \(2u=8k\), and they have equal signs exactly when \(j-u\) is \(0,1,\) or \(8k+2\). Since column 0 is outside the displayed set, normalizing that column by row signs reverses the tetrad product. Its negative positions after normalization are precisely the twelve displayed columns \(J\).

The four tetrad rows are pairwise exactly orthogonal. The thirteen columns \(J\cup\{0\}\) are also pairwise exactly orthogonal. Cross-block Gram entries vanish by the Goethals–Seidel identity. The only within-block cyclic shifts needed, up to reversal, are \(1,u,u+1,2u,2u+1\). Their exact combined cyclic correlations vanish. Here is a finite way to check this for every \(k\).

For each shift \(\ell\) on that list, the combined cyclic coefficient is
\[
 \sum_{i\bmod t} s_i s_{i+\ell}
 (1+\tau_i\tau_{i+\ell})(1+q_i q_{i+\ell}).
\]
The sign patterns of \(s,q,\tau\) are 8-periodic within the intervals cut by
\[
 0,u,2u,2u+1,2u+2,2u+3,2u+5,3u+1,3u+2,3u+5,4u+1,4u+2,t,
\]
with phase determined by \(k\bmod8\). Cut further at the translates of these points by \(-\ell\) and \(t-\ell\). The interval endpoints are affine integer expressions in \(k\). For each starting value \(k_0=8,\ldots,15\), order these expressions by their values at \(k_0\), breaking ties by slope. The adjacent differences have nonnegative slopes and nonnegative values at \(k_0\), so that order holds for all \(k\ge k_0\). On each resulting interval and each \(k\bmod8\), the count of indices in each residue class modulo 8 is affine in \(k\). The cyclic coefficient is therefore affine on each such progression. The [exact verifier](defect12_mod32_construction.py) evaluates both \(k_0\) and \(k_0+8\), obtaining zero in each case, and checks \(1\le k<8\) directly.

## Reflection and primitivity

Reflect the tetrad by \(J_4/2-I_4\). Columns outside \(J\) stay signs, and the twelve removed columns acquire one spike \(\pm2\) each on the tetrad. Let \(A\) be the kept columns and \(R=2V\) the removed columns. Exact orthogonality of the selected columns gives \(R^{\mathsf T}R=nI_{12}\) and zero column sums. Exact orthogonality of the tetrad rows gives squared norm 12 in \(R\) on the tetrad, so the four spike rows each have support of size three. The other rows of \(R\) are signs.

The reflection reduces 64-modular row orthogonality to at least 32-modular orthogonality. In the tetrad block, the symmetric integral coefficient of the error has zero diagonal, so the sum of its entries is even and the two factors of \(1/2\) cost only one power of 2. Outside the tetrad block at most one factor of \(1/2\) occurs. The column Gram of \([A\ R]\) stays 64-modular. Replacing \(R\) by \(RB\) costs at most one power of 2 in the cross term and \(R^{\mathsf T}R\) is exact.

Modulo 4, the dot product of each spike row with any sign row of \(R\) is 2. The row Gram congruence forces every sign row of \(R\) to have the same product, as in [MOD16_DEFECT12_FAMILY.md](MOD16_DEFECT12_FAMILY.md). Negate one residual column if necessary so that the common sign-row product is negative. All doubled residual rows then have coordinate sum 2 modulo 4. Both shadow types are present, and the row products of \(A\) distinguish the two types after choosing a spike row as the first row and normalizing its signs.

The minor in block-0 rows
\[
 0,1,3,u,u+1,u+2,u+3,u+5,u+6,3u+2,3u+3,3u+4
\]
and columns \(J\) has determinant of magnitude \(65536=2^{16}\). For \(k\ge8\), its signs are constant on each residue class of \(k\bmod8\) by the same affine interval test. One set of row words, in hexadecimal with bit 1 denoting a negative sign, is
\[
 \mathtt{0c1,453,9e0,9f2,97c,c98,a6b,34a,106,7f9,668,f32}.
\]
The other set has its first three rows negated. The verifier checks both possibilities and the finite values \(k<8\). These rows are outside the tetrad, so normalizing by row signs and choosing the shadow convention affect only the sign of the determinant.

For the lattice \(L\) generated by the rows of \(V\), the minor gives an index in \(D_{12}^{*}\) dividing \(2^{16}/2^{11}=32\). The frame identity gives \(tD_{12}\subseteq L\), and the two shadow types generate \(D_{12}^{*}/D_{12}\). Thus the same index is odd, so \(L=D_{12}^{*}\). This proves the primitive shadow and the two augmented Gram congruences. At \(k=1\) the verifier checks that the source \(H\) is exactly orthogonal. In that case any additional sign column would give a norm-one vector of \(D_{12}^{+}\), which has minimum squared norm 2. See [the exact obstruction argument](DEFECT12_EXACT.md).

## A separate order-156 certificate

At \(t=39\), use the \(k=1\) instance of the \(32k+7\) source from Eliahou's Construction 6.2. Its run lengths are
\[
 q=(19,2,17,1),\qquad
 s=(4,2,1,1,1,5,2,1,1,2,1,1,3,1,2,1,3,3,1,2,1).
\]
Use global zero-based tetrad rows \((68,49,107,88)\), normalizing column 2, and removed columns \((9,11,29,49,67,69,88,106,108,127,145,147)\). The minor on rows \((0,1,3,9,10,11,12,13,14,28,29,31)\) again has absolute determinant \(65536\). The verifier checks the exact frame and both modulo-32 identities directly at this order and at \(t=19,35,51,67\) from the main family.
