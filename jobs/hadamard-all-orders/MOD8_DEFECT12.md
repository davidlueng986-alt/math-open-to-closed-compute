# A defect-12 \(D_{12}^{+}\) model modulo 8

The determinant-one \(D_{12}^{+}\) branch in [OVERLATTICES.md](OVERLATTICES.md) passes a simultaneous mod-8 test of the two Gram identities in integral lattice coordinates. This holds at \(t=599\). The construction works for \(t\equiv3\pmod4\) with \(t\ge87\) or \(t\equiv1\pmod4\) with \(t\ge165\).

## Statement

Let \(n=4t\), \(k=n-12\), and use the Euclidean lattice
\[
 D_{12}=\{a\in\mathbb Z^{12}:\sum_j a_j\equiv0\pmod2\},\quad
 h=\tfrac12(1,\ldots,1),\quad U=D_{12}^{+}=D_{12}\cup(h+D_{12}).
\]
The lattice \(U\) is odd unimodular, its even sublattice is \(D_{12}\), and it has no vectors of norm squared 1. There exist \(n\) rows \(\rho_i\in D_{12}^{*}\setminus U\), with both integral and half-integral rows present, and a normalized sign matrix \(A_0\in\{\pm1\}^{n\times k}\) satisfying the following conditions.

- The row lattice is \(D_{12}^{*}\). Every row has \(\|\rho_i\|^2=3\). The rows sum to zero and the matrix \(V\) with rows \(\rho_i\) satisfies \(V^{\mathsf T}V=tI_{12}\).
- The product of row \(i\) of \(A_0\) is positive for integral \(\rho_i\) and negative for half-integral \(\rho_i\).
- For any integral basis \(B\) of \(U\) written in columns, let \(K=B^{\mathsf T}B\), \(C=2VB\), \(P=[A_0\ C]\), and \(D=\operatorname{diag}(I_k,K)\). The matrices \(P\) and \(D^{-1}\) are integral, and
  \[
  P^{\mathsf T}P\equiv nD\pmod8,\qquad
  PD^{-1}P^{\mathsf T}\equiv nI_n\pmod8.
  \]

Thus the sign columns are orthogonal modulo 8, the overlaps with the residual frame satisfy \(V^{\mathsf T}A_0\subseteq 4U\) columnwise, and \(A_0A_0^{\mathsf T}+4VV^{\mathsf T}\equiv nI_n\pmod8\). The identities for an actual partial Hadamard require equality over the integers. The model leaves that equality and the existence of a defect-12 partial Hadamard with this residual lattice open.

## Construct the shadow frame

The dual \(D_{12}^{*}\) is \(\mathbb Z^{12}\cup(h+\mathbb Z^{12})\). Its complement of \(U\) consists of odd-sum integer vectors and odd-sum half-integer vectors. A sparse block partitions the 12 coordinates into four triples and places the four sign rows
\[
 (1,1,1),\ (1,-1,-1),\ (-1,1,-1),\ (-1,-1,1)
\]
on each triple, with zeros elsewhere. Each block has 16 shadow rows, zero sum, and covariance \(4I_{12}\). Coordinate sign changes within a triple preserve these properties. Negating individual rows preserves the covariance, and each negation subtracts twice the original row from the sum.

A half-integer block takes the rows of a normalized Hadamard matrix of order 12, negates column 1, and divides by 2. Use indices starting at 0, with column 0 the constant column. For example, take the Paley matrix with initial row and column all positive and lower square \((\chi(j-i)-[i=j])_{i,j\in\mathbb F_{11}}\), where \(\chi(0)=0\) and \(\chi\) is the quadratic character. Before the column negation every row has an even number of negative signs. The resulting half-integer rows have odd coordinate sum. The block has covariance \(3I_{12}\) and sum \(6e_0\).

Use \(a=1\) half-integer block for \(t\equiv3\pmod4\) and \(a=3\) for \(t\equiv1\pmod4\). Use \(r=(t-3a)/4\) sparse blocks. In a group of three sparse blocks choose signs and triples to include the rows
\[
 e_0+e_1+e_2,\qquad -e_1+e_3+e_4,\qquad -e_2-e_3-e_4.
\]
Their sum is \(e_0\). Negate these three rows in each of \(3a\) groups of sparse blocks. This subtracts \(6ae_0\) from the row sum. The full frame has \(16r+12a=4t\) rows, sum zero, and covariance \(tI_{12}\).

Reserve twelve other sparse blocks, one for each of the ten triples \(\{0,1,j\}\) for \(2\le j\le11\), and the triples \(\{0,2,3\}\), \(\{1,2,3\}\). The triple indicators span \(\mathbb F_2^{12}\). A word orthogonal to the ten indicators has \(v_j=v_0+v_1\) for \(j\ge2\), and the last two indicators give \(v_0=v_1=0\). The signed rows on each triple generate twice each coordinate vector on that triple by pair sums. The integer rows therefore span \(\mathbb Z^{12}\), and a half-integer row adds the coset \(h+\mathbb Z^{12}\). The number of sparse blocks needed is \(12+9a\), which gives the two bounds on \(t\). At \(t=599\) there are 149 sparse blocks and one half-integer block.

The even-total integer combinations of the rows generate exactly \(U\), since the rows generate the full dual and each lies in its nontrivial coset modulo \(U\). This realizes the determinant-one case of the residual lattice in [OVERLATTICES.md](OVERLATTICES.md).

## Construct the binary columns

Write \(E=\mathbf1_n^\perp\subseteq\mathbb F_2^n\) for the even words, with pairing \(x\cdot y\) and quadratic form \(q(x)=\mathrm{wt}(x)/2\bmod2\). Choose \(\rho_0\) to be an integer row. For \(b\in U/2U\) put
\[
 \lambda(b)=\|b\|^2\bmod2,\qquad
 g_b(i)=\langle b,\rho_i-\rho_0\rangle\bmod2,\qquad
 c_0=2\rho_0\bmod2U.
\]
The rows belong to a single coset modulo \(U\). Pairing \(b\) with any row lies in \(\mathbb Z+\lambda(b)/2\), since \(D_{12}\) is the even sublattice. In particular \(\langle b,c_0\rangle\bmod2=\lambda(b)\), and \(\lambda(c_0)=0\). The even weight of \(g_b\) follows by summing its entries and using the zero row sum. The frame identities give
\[
 g_b\cdot g_c=\langle b,c\rangle+\lambda(b)\lambda(c)\pmod2,\qquad
 q(g_b)=\frac{\|b\|^2+\lambda(b)}2\bmod2 .
\]
For the second formula, the weight modulo 4 equals the sum of the squares of the integer pairings with the differences. That sum is \(t\|b\|^2+n\langle b,\rho_0\rangle^2\equiv t(\|b\|^2+\lambda(b))\pmod4\).

The first formula is nonsingular as a pairing on \(U/2U\). A kernel element would satisfy \(b+\lambda(b)c_0=0\) by unimodularity, and then applying \(\lambda\) gives \(\lambda(b)=0\). Thus \(G=\{g_b\}\) is a nonsingular quadratic subspace of dimension 12.

Its quadratic Gauss sum is \(-64\). Indeed, the even-norm classes \(D_{12}/2U\) map to the even binary words of length 12 modulo the all-one word with two lifts each. For those classes the quadratic value is \(\mathrm{wt}/2\bmod2\), which agrees for a word and its complement, so the contribution is \(\Re(1+i)^{12}=-64\). The odd-norm classes cancel in pairs under the translation \(b\mapsto b+2e_0\), since \(e_0\notin U\) and the norm squared changes by \(4b_0+4\equiv2\pmod4\).

The form on \(E\) has the all-one word in its radical with \(q(\mathbf1_n)=0\). Its Gauss sum is \(\Re(1+i)^n=-2^{n/2}\) for odd \(t\). The nonsingular quotient \(E/\langle\mathbf1_n\rangle\) and \(G\) each have Arf invariant 1. The orthogonal complement of \(G\) in the quotient has dimension \(n-14\) and Arf invariant 0. Identify it with
\[
 W_0=(G^\perp\cap E)\cap\{x:x(0)=0\}
\]
using the unique representatives with coordinate 0 zero. Set \(m=n-13\) and let \(E_m\) be the even words of length \(m\). The form on \(E_m\) is nonsingular because \(m\) is odd, and its Gauss sum is \(\Re(1+i)^m=2^{(m-1)/2}\) because \(m\equiv7\pmod8\). By the classification of nonsingular binary quadratic forms, there is an isometry \(\phi:W_0\to E_m\).

For \(1\le j\le m\), put \(y_j=\phi^{-1}(\mathbf1_m+e_j)\). These \(y_j\) sum to zero, each has quadratic value 1, and distinct ones have pairing 1. Let \(w=g_{c_0}\). Its \(i\)-th bit is 0 on integral \(\rho_i\) and 1 on half-integral \(\rho_i\), by the formula for \(c_0\) and because \(\rho_0\) has odd coordinate sum. Its quadratic value is \(12/2\bmod2=0\). Use \(x_j=w+y_j\) as the sign bits of column \(j\), with the additional constant positive column 0. These words vanish at coordinate 0. They sum to \(w\), have weight 2 modulo 4, and distinct ones have pairings 1 modulo 2. These conditions give the asserted row products and \(A_0^{\mathsf T}A_0\equiv nI_k\pmod8\).

## Check both Gram identities

For a nonconstant column \(x=x_j\), its pairing with \(g_b\) equals \(g_{c_0}\cdot g_b=\lambda(b)\). The frame-weighted sum \(\sum_i x(i)\rho_i\) pairs evenly with every \(b\in U\). Its pairing modulo 2 is the sum of \(g_b\cdot x=\lambda(b)\) and \(\mathrm{wt}(x)\langle b,\rho_0\rangle\equiv\lambda(b)\pmod2\). The sum is therefore in \(2U\) by unimodularity. Since the rows sum to zero, the sign column gives twice the negative of that sum, which lies in \(4U\). The constant column pairs to zero. Consequently \(C^{\mathsf T}A_0\equiv0\pmod8\) and \(C^{\mathsf T}C=nK\).

For distinct row indices \(i,\ell\) set \(u=\rho_i-\rho_\ell\in U\), \(\lambda=\lambda(u)\). Decompose
\[
 e_i+e_\ell=g_b+v+\alpha\mathbf1_n,\qquad
 b=u+\lambda c_0\bmod2U,\quad v\in W_0.
\]
This formula for \(b\) follows by pairing with every \(g_c\). The binary difference of rows \(i,\ell\) across the \(m\) nonconstant columns is \(\phi(v)+\lambda\mathbf1_m\). Indeed, \(y_j\cdot(e_i+e_\ell)\) is \((\mathbf1_m+e_j)\cdot\phi(v)=\phi(v)_j\), while \(w\cdot(e_i+e_\ell)=\lambda\). The even word \(\phi(v)\) has weight congruent modulo 4 to
\[
 2q(v)=2+\|b\|^2+\lambda\pmod4.
\]
Here \(q(e_i+e_\ell)=1\) and \(\|b\|^2\equiv\|u\|^2+2\lambda\pmod4\). If \(\lambda=0\), the row distance is \(2+\|u\|^2\equiv2-\|u\|^2\pmod4\). If \(\lambda=1\), the complement in length \(m\equiv3\pmod4\) gives the same \(2-\|u\|^2\pmod4\). This equals
\[
 \frac{k+4\langle\rho_i,\rho_\ell\rangle}{2}\pmod4,
\]
since \(k\equiv0\pmod8\) and \(\|\rho_i\|^2=\|\rho_\ell\|^2=3\). Thus \(A_0 A_0^{\mathsf T}+4VV^{\mathsf T}\equiv nI_n\pmod8\) off the diagonal, and the diagonal equals \(n\) exactly. The two displayed congruences for \(P\) follow.

[The exact verifier](defect12_mod8.py) uses the Python standard library. It constructs the frame and the sign bits at \(t=599\), produces the quadratic isometry by hyperbolic decomposition, and checks the frame covariance and the two Gram congruences directly using integer arithmetic.
