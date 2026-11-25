# An exact \(D_{12}^{+}\) obstruction at order 28

There is a normalized \(28\times16\) partial Hadamard to which no orthogonal sign column can be appended. Its residual frame has row lattice \(D_{12}^{*}\), and the even-total row combinations generate the determinant-one lattice \(D_{12}^{+}\). This is an exact example of the branch in [OVERLATTICES.md](OVERLATTICES.md). The [mod-8 construction](MOD8_DEFECT12.md) applies to a separate family of orders.

## Fixed construction

Index rows and columns from zero. Construct the normalized Paley Hadamard \(H\) of order 28 over \(F=\mathbb F_3[X]/(X^3-X-1)\). The field elements are indexed by \(a_0+3a_1+9a_2\), where \(a_i\in\{0,1,2\}\) are their polynomial coefficients. Row and column 0 are all positive. The remaining square has entries \(\chi(j-i)-[i=j]\) for field elements \(i,j\) in index order, with \(\chi\) the quadratic character and \(\chi(0)=0\).

Take rows \(I=(0,1,2,4)\). Their entrywise product is negative exactly on the columns
\[
 J=(1,4,6,11,13,14,15,16,22,24,25,26).
\]
On the four rows in \(I\), apply the orthogonal reflection \(J_4/2-I_4\), where \(J_4\) is all ones. For a column in the complement of \(J\), the tetrad entries remain signs. For a column in \(J\), the tetrad has one entry \(2\) or \(-2\) and three zero entries. All rows outside \(I\) are untouched. Set \(A\) equal to the 16 kept columns and normalize its first row by column signs. Set \(R\) equal to the 12 removed columns after the reflection, in their original order.

The square matrix \([A\ R]\) has both Gram matrices equal to \(28I_{28}\). In particular \(R^{\mathsf T}R=28I_{12}\), \(A^{\mathsf T}R=0\), and the rows of \(R\) sum to zero. The four tetrad rows each contain three nonzero entries, with disjoint supports, and every remaining row is a sign vector. All rows of \(R\) have squared norm 12 and coordinate sum 2 modulo 4. The determinant of the \(12\times12\) matrix of rows
\[
 (0,1,2,3,4,5,6,7,8,10,11,13)
\]
of \(R\) is \(-20480\), which is \(2\) modulo 7. The [standalone verifier](defect12_exact.py) checks these identities with integer and rational arithmetic. For background on quadruple and Hall-set switching of full Hadamards, see [Orrick, *Switching operations for Hadamard matrices*](https://arxiv.org/abs/math/0507515).

## Lattice and obstruction

Let \(\rho_i=R_i/2\) and \(L=\sum_i\mathbb Z\rho_i\). Use
\[
 D_{12}=\{a\in\mathbb Z^{12}:\textstyle\sum a_j\equiv0\pmod2\},\qquad
 h=\tfrac12\mathbf1,\qquad U=D_{12}^{+}=D_{12}\cup(h+D_{12}).
\]
The rows have squared norm 3. The tetrad rows have odd integer coordinate sum, and the other rows have odd coordinate sum in \(h+\mathbb Z^{12}\). These two types lie in different nonzero classes of \(D_{12}^{*}/D_{12}\cong(\mathbb Z/2)^2\) and generate the quotient. Here
\[
 D_{12}^{*}=\mathbb Z^{12}\cup(h+\mathbb Z^{12}).
\]

For any \(d\in D_{12}\), all \(\langle d,\rho_i\rangle\) are integral and the frame identity gives \(7d=\sum_i\langle d,\rho_i\rangle\rho_i\in L\). Thus \(D_{12}^{*}/L\cong D_{12}/(L\cap D_{12})\) is a 7-group. The twelve rows in the minor generate a sublattice of \(L\) of covolume \(20480/2^{12}=5\), so \([D_{12}^{*}:L]\) also divides \(5/(1/2)=10\). This forces \(L=D_{12}^{*}\). All the rows lie in the unique nontrivial class of \(D_{12}^{*}/U\). The even-total row combinations therefore equal \(U\).

If a new sign column \(z\) were orthogonal to \(A\), it would be \(z=Ry\) for some \(y\in\mathbb R^{12}\). Since \(\|z\|^2=28\) and \(R^{\mathsf T}R=28I_{12}\), one has \(\|y\|^2=1\). Also \(\langle y,\rho_i\rangle=z_i/2\in\{1/2,-1/2\}\), so \(y\) pairs integrally with the even-total row combinations and belongs to \(U^{*}=U\). The integer vectors of \(U\) have even coordinate sum, and the half-integer vectors have squared norm at least 3. Hence \(U\) has no norm-one vectors, which proves the obstruction.

The Hadamard at this order is given by \(H\) itself. The example shows that full existence can coexist with an exact maximal prefix stopping 12 columns short. An independent binary replay leaves 2,048 sign masks up to overall sign under the necessary parity equations. Of these, 586 have the right weight and none has all 15 exact intersections.
