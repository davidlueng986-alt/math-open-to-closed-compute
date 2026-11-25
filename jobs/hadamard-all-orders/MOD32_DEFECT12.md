# A modulo-32 obstruction for the Eliahou–Kervaire source

The Goethals–Seidel source used in [MOD16_DEFECT12_FAMILY.md](MOD16_DEFECT12_FAMILY.md) cannot give a simultaneous modulo-32 model by a single reflection of four pairwise exactly orthogonal rows. Separately, its twelve original residual columns cannot give the modulo-32 column Gram in the standard \(D_{12}^{+}\) coordinates if they form an exact residual panel. Both statements apply for \(t=4r+3\), \(r\ge4\), including \(t=599\). They concern the specified source and operations. The existence of a modulo-32 model with a different source or frame remains open here.

## The two necessary error masks

Set \(t=4r+3\), \(n=4t\), and let \(H\) be the source in Eliahou and Kervaire, *A survey on modular Hadamard matrices*, array (3) and Theorem 3.2.2. Both \(HH^{\mathsf T}-nI\) and \(H^{\mathsf T}H-nI\) are equal to \(32E\), where \(E\) has four identical circulant blocks of order \(t\) on its diagonal. The Goethals–Seidel Gram formula gives the row version. Its block is a symmetric circulant and commutes with both circulants and reversal, so \(H\) commutes with \(HH^{\mathsf T}\). The latter is invertible because \((HH^{\mathsf T})/4\) is the identity modulo 2. This gives the column version. The block coefficients follow by periodizing the published aperiodic coefficients. [Open-access survey](https://morfismos.cinvestav.mx/sites/default/files/Upload/vol07-n2-2.pdf)

Let \(I\) be a tetrad of exactly orthogonal source rows. Row sign normalization leaves \(E\bmod2\) unchanged. The reflection \(J_4/2-I_4\) sends the row Gram error between an outside row \(i\) and a tetrad row \(j\) to
\[
 32\left(\frac12\sum_{\ell\in I} E'_{i\ell}-E'_{ij}\right),
\]
where \(E'\) is the signed error and \(E'\equiv E\bmod2\). Divisibility by 32 requires \(\sum_{\ell\in I}E_{i\ell}\equiv0\bmod2\). This already holds within \(I\) by exact orthogonality. Consequently the row Gram congruence requires
\[
 E\mathbf1_I=0\pmod2.
\]
For a residual matrix \(R=2V\) and a basis \(B\) of \(D_{12}^{+}\), the weighted row Gram of \([A\ RB]\) is \(AA^{\mathsf T}+RR^{\mathsf T}\), so this condition applies to the augmented model.

For the other condition, let \(J\) be the twelve original source columns selected for the residual, with exact Gram \(R^{\mathsf T}R=nI\). Orthogonal row operations preserve the source column Gram. Column signs and permutations can be accounted for in the source labels and leave the error parity unchanged. The vector \(h=\tfrac12\mathbf1_{12}\) belongs to \(D_{12}^{+}\), so the augmented column Gram congruence in the standard \(D_{12}^{+}\) coordinates requires \(A^{\mathsf T}Rh\equiv0\bmod32\). In terms of the source error, this requires \(\sum_{\ell\in J}E_{i\ell}\equiv0\bmod2\) for every retained column \(i\). It also holds within \(J\) by exactness of the panel. Thus the column Gram congruence requires
\[
 E\mathbf1_J=0\pmod2.
\]

## The binary error kernel has minimum weight at least 15

Let \(m=\lfloor r/2\rfloor\). Work in \(\mathbb F_2[x]/(x^t-1)\). Each binary error block acts by multiplication by
\[
 F(x)=\sum_{\substack{1\le i<m\\m-i\ \mathrm{odd}}}
 (x^{2i}+x^{-2i}).
\]
This is the reduction of the aperiodic error coefficients \(m-i\) at shifts \(2i\) and \(-2i\). Since \(t\) is odd, \(x^t-1\) is squarefree.

For even \(m\), the shifted polynomial \(x^{2(m-1)}F\) equals \(\sum_{j=0}^{m-1}x^{4j}\). Its greatest common divisor with \(x^t-1\) is \(x^d-1\), with \(d=\gcd(t,m)\). For a nontrivial \(t\)-th root \(\alpha\), multiplying the sum by \(1+\alpha^4\) reduces the condition to \(\alpha^m=1\). The root 1 belongs as \(m\) is even. Thus the kernel is the space of words of period \(d\), and its minimum nonzero weight is \(t/d\).

For odd \(m\), the shifted polynomial omits the middle term \(x^{2(m-1)}\) from that same sum. Multiplying it by \(1+x^4\) gives
\[
 (1+x^{2(m-1)})(1+x^{2(m+1)}).
\]
The root 1 again belongs to the kernel polynomial. The remaining common roots with \(x^t-1\) have orders dividing \(d_-=\gcd(t,m-1)\) or \(d_+=\gcd(t,m+1)\). These periods are coprime. The kernel is the sum of the two spaces of period \(d_-\) and period \(d_+\). Each period space lies in the kernel and their intersection consists of constants, so their sum has the dimension \(d_-+d_+-1\) given by the greatest common divisor.

Inside a period of length \(d_-d_+\), a word in this sum has the form \(a_i+b_j\) on the rectangular array of residue pairs. Two rows are complements if \(a_i\) varies, and two columns are complements if \(b_j\) varies. A nonzero period has weight at least \(\min(d_-,d_+)\), and the bound is realized by a single nonzero residue in the larger period. The minimum nonzero length-\(t\) weight is therefore \(t/\max(d_-,d_+)\).

Writing \(t=8m+3\) or \(8m+7\) bounds \(d\le7\) and \(\max(d_-,d_+)\le15\). Hence the minimum is at least 15 for \(t\ge225\). Below 225 the same formulas give minimum at least 15 for each \(4\le r\le55\), with equality at \(t=75\). The [exact polynomial verifier](defect12_mod32.py) checks this finite range and the \(t=599\) calculation. At \(t=599\), the kernel in each circulant block consists only of constants, and for the specific tetrad and residual panel in [MOD16_DEFECT12.md](MOD16_DEFECT12.md) the two error masks have image weights 296 and 888, respectively.

The kernel of the four-block error has the same minimum nonzero weight as one block. Neither a weight-four mask nor a weight-twelve mask can lie in it. The case \(r\le3\) instead has zero error and gives the exact examples in [MOD16_DEFECT12_FAMILY.md](MOD16_DEFECT12_FAMILY.md).

## Any Goethals–Seidel source at \(t=599\)

The mask obstruction at \(t=599\) extends to every 32-modular Goethals–Seidel source of this order. The source formula again gives identical symmetric circulant error blocks. Let \(F\) describe such a block modulo 2, with degree less than 599 and zero constant coefficient from the zero Gram diagonal error. Since \(599\) is prime and \(2\) has order \(299\) modulo \(599\), the powers of 2 and inversion together act transitively on the nontrivial 599th roots of unity over \(\overline{\mathbb F}_2\). Indeed \(299=13\cdot23\), with \(2^{299}=1\), \(2^{13}=405\) and \(2^{23}=212\) modulo 599. Inversion lies outside the odd-order subgroup generated by 2.

If \(F\) vanishes at a nontrivial root, it vanishes at every such root by Frobenius and symmetry. Then \(F\) is zero or a multiple of \(1+x+\cdots+x^{598}\) of degree at most 598. The nonzero multiple would have constant coefficient 1. Thus every nonzero symmetric error polynomial has no nontrivial common root with \(x^{599}-1\). Its only common root is 1, since its coefficients occur in symmetric pairs, and the kernel consists only of constants. Consequently either exact-panel mask requires a 64-modular source at \(t=599\) within the Goethals–Seidel construction.

An alternate 64-modular source would suffice if it has four exactly orthogonal rows whose product identifies twelve columns, an exact twelve-column residual panel, a kept column exactly orthogonal to that panel, and the required primitive \(D_{12}^{+}\) shadow after reflection. The same error calculation loses at most one power of 2 in the row Gram because the symmetric tetrad error has zero diagonal. The basis change loses at most one in the column Gram. The existence of a 64-modular sign matrix alone supplies neither the exact panel nor the shadow lattice.

## Row checks at any power of two

The Schur reduction in [MOD16_DEFECT12.md](MOD16_DEFECT12.md) extends from 16 to \(2^s\) for every \(s\ge3\). Let \(n=4t\) with \(t\) odd and \(P\) be integral with first column \(\mathbf1_n\) and constant parity within each column. Put \(D=\operatorname{diag}(1,D_1)\), where \(D_1\) is integral symmetric unimodular. Let \(r=P_{0,1:}\) and suppose \(rD_1^{-1}r^{\mathsf T}=n-1\). Set \(v=n-1\), \(\mathbf1=\mathbf1_v\),
\[
 p=D_1^{-1}r^{\mathsf T},\qquad S=(P_{1:,1:}-\mathbf1r)/2 .
\]
If \(P^{\mathsf T}P\equiv nD\bmod2^s\), then
\[
 PD^{-1}P^{\mathsf T}\equiv nI\bmod2^s
 \quad\Longleftrightarrow\quad
 Sp\equiv-2t\mathbf1\bmod2^{s-1}.
\]

Indeed, the block factorization in the modulo-16 proof gives
\[
 \mathbf1^{\mathsf T}S\equiv-2tr\bmod2^{s-1},\qquad
 S^{\mathsf T}S\equiv t(D_1+r^{\mathsf T}r)\bmod2^{s-2}.
\]
Over \(\mathbb Z/2^{s-2}\), \(p\) and \(\mathbf1\) have unit norm \(v\) in their respective spaces. The same restriction of \(S\) is a similitude \(p^\perp\to\mathbf1^\perp\) of odd multiplier \(t\), so \(Sp\equiv-2t\mathbf1\bmod2^{s-2}\). The operator \(SD_1^{-1}S^{\mathsf T}\) acts by \(t\) on \(\mathbf1^\perp\) and by \(4t^2\) on \(\mathbf1\). Since \(4t^2-t=t(n-1)\), it is \(t(I+\mathbf1\mathbf1^{\mathsf T})\) modulo \(2^{s-2}\). The remaining block in the row Gram is \(2Sp\). Equivalently, its error in the original coordinates is
\[
 2^{s-1}(\mathbf1_n\tilde d^{\mathsf T}+\tilde d\mathbf1_n^{\mathsf T})\bmod2^s,\qquad
 \tilde d=\left(0,\frac{Sp+2t\mathbf1}{2^{s-2}}\bmod2\right).
\]
Its vector \(\tilde d\) has even weight by the column margin relation. Thus, after checking the column congruence, the pairings with the first row determine the other Gram congruence at every power of two.
