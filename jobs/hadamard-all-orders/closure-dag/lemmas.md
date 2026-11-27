# Connecting proofs

Write $H(n)$ for existence of an $n\times n$ sign matrix with orthogonal columns. For a square real matrix this is equivalent to $HH^{\mathsf T}=nI$. Let $D$ be the odd $t\ge5$ left after the two direct Paley tests and the Scarpis–Đoković test in the [all-order reduction](../README.md). Put $n=4t$, $b=2t-1$, $k=t-1$, $m=2b$, $h=2t-8$. Below, $J$ is an all-ones matrix of the indicated size. The two copies of the row set $[b]$ have separate labels. Point labels within $[b]$ are common.

## Pivot

An outside design $Y$ has $2b$ blocks of size $t$ on $2t$ points, every point has degree $b$ and every distinct pair has codegree $k$. Mark any point $\infty$. Exactly $b$ blocks contain it. Delete $\infty$ from those blocks to form the rows of $A$. For the other $b$ blocks take their complements in the $b$ finite points to form the rows of $B$. Both are $b\times b$ binary matrices with all row and column sums $k$. For a finite point, its degree in $A$ is its codegree with $\infty$, and its degree in $J-B$ is $b-k=t$.

For the finite points the Gram matrix is $tI+kJ$. Since $B$ is column-regular, $(J-B)^{\mathsf T}(J-B)=J+B^{\mathsf T}B$. Thus the exact requirement is

$$A^{\mathsf T}A+B^{\mathsf T}B=tI+(t-2)J. \tag{1}$$

Conversely two binary $k$-regular matrices satisfying (1) give $Y$ by taking $(\mathbf1,A)$ above $(\mathbf0,J-B)$. The row sizes, degrees and pair codegrees follow from the displayed formulas, including pairs with $\infty$. Row orders in each half can be chosen independently. This proves equivalence with R for every $t\in D$.

## Signature

Write the indicator of a prospective inner column as $(u,v)$ on the two row sets. Its total size must be $2k$ and its overlap with the pivot column must be $k$. These say exactly $|u|=|v|=k$. Its vector of overlaps with finite points is $A^{\mathsf T}u+(J-B)^{\mathsf T}v=k\mathbf1+A^{\mathsf T}u-B^{\mathsf T}v$. Thus the remaining mixed equations are exactly

$$ A^{\mathsf T}u=B^{\mathsf T}v. \tag{2}$$

For fixed $A,B$, these pairs form the vertex set of a graph. Two distinct vertices are adjacent when $u^{\mathsf T}u'+v^{\mathsf T}v'=t-2$. A $j$-clique is precisely $j$ mutually valid inner columns with all prescribed mixed and inside intersections. This equivalence uses the same $A,B$ and labels for every vertex.

Define $N_j(A,B)$ to be the number of unordered $j$-cliques. The older assembly gives $1+2t+j$ orthogonal sign columns. Consequently $N_h>0$ on **some** pair satisfying (1) gives $H(4t)$ by Verheiden. Capacity constraints are unnecessary for this implication. Conversely a full Hadamard matrix supplies $N_b>0$ for some such pair by normalization and extraction. Thus at each $t\in D$, the existential $h$-clique criterion is equivalent to $H(4t)$. One empty fixed graph or one graph of small clique number concerns only its own pair. [Assembly](../Assembly.lean) · [Seven-column completion](https://doi.org/10.1016/0097-3165(80)90028-X)

For the first slot let $a(s)$ count the $k$-subsets of rows of $A$ with vector of column sums $s$, and define $b(s)$ for $B$ in the same way. Then $N_1=\sum_s a(s)b(s)$. Computing the two histograms requires no clique search. Equivalently the two multisets of signatures are the degree-$k$ coefficients in $\prod_r(1+w x^{A_r})$ and $\prod_r(1+w x^{B_r})$, with $x^p=\prod_i x_i^{p_i}$. A positive coefficient in common is exactly one selector. For every pair satisfying (1), a constant fractional selection gives the same signature on both sides. The integer supports still have to meet.

With previously chosen $(u_i,v_i)$ for $i<j$, compare the augmented keys

$$\left(A^{\mathsf T}u,(u^{\mathsf T}u_i)_{i<j}\right),\qquad
\left(B^{\mathsf T}v,(t-2-v^{\mathsf T}v_i)_{i<j}\right).$$

Restrict each enumeration to the size-$k$ subsets respecting forced zeros and ones on its own half. A matching key is **equivalent** to a next column on this fixed prefix with all capacities preserved. The equations for the old columns are exactly the extra key coordinates. This supplies positive witnesses as row labels and an exact local failure certificate as two disjoint signature histograms.

After the forced bits are removed, write the remaining integer system as $Mx=y$. The known fractional solution has denominator $s=b-j$, so some integer vector $p$ satisfies $Mp=sy$. In particular the class of $y$ in $\mathbb Z^{\#\mathrm{equations}}/M\mathbb Z^{\#\mathrm{free\ bits}}$ has finite order dividing $s$. Modulo any prime not dividing $s$ the equation is already solvable. An obstruction from this lattice must therefore involve a divisor of $s$; a binary-cube obstruction can remain even when all integer lattice tests pass. [Fractional identity](../Rounding.lean)

## Regular switches

Regular pairs exist before imposing (1), for instance take a circulant matrix with ones in its first $k$ shifts for each member. For finite points $i\ne j$ define

$$D_{ij}=(A^{\mathsf T}A+B^{\mathsf T}B)_{ij}-(t-2),\qquad E=\sum_{i<j}D_{ij}^2.$$

Set $D_{ii}=0$. Every row sum of $D$ vanishes because $2k(k-1)=(b-1)(t-2)$. The diagonal of (1) already holds. Thus $E=0$ is equivalent to (1). If $E>0$, then $E\ge4$. With $E\le4$, one entry of magnitude two cannot have zero signed incidence at its endpoints on its own. For entries of magnitude one every incident vertex needs both signs and has even degree. A simple graph on at most four edges with these properties has to be an alternating four-cycle. A triangle cannot alternate. Therefore $E=4$ is the unique smallest possible positive shape, up to relabelling and reversal of signs. This classification does not assert it is attained for every $t$.

Take rows $r,s$ and columns $u,v$ of $A$ with diagonal ones and off-diagonal zeros, and switch the four entries. This preserves every row and column sum. Write $\delta_w=A_{sw}-A_{rw}$ for $w\notin\{u,v\}$, using the old entries. The only changed defects are $D_{uw}\mapsto D_{uw}+\delta_w$ and $D_{vw}\mapsto D_{vw}-\delta_w$. In particular

$$E'-E=2\sum_{w\ne u,v}\delta_w(D_{uw}-D_{vw}+\delta_w).$$

The same formula holds for a switch in $B$. At $E=4$, write the positive edges as $uw,vx$ and the negative edges as $ux,vw$. There is a one-switch repair exactly when one of the matrices has two rows whose respective set differences are $\{u,w\}$ and $\{v,x\}$. Indeed both switched columns must touch all four bad edges and their mutual entry stays fixed, so they form an opposite pair, say $u,v$. The formula then forces $\delta_w=-1,\delta_x=1$ and zero on every other column outside $u,v$. These are exactly the stated row differences; switching $u,v$ clears all four errors. The other opposite pair gives the same criterion.

If every $E>4$ state admits a finite switch path with endpoint at lower energy and every $E=4$ state can reach zero, strong induction on the integer $E$ constructs an outside design. The task cards test the stronger version with intermediates of energy at most the starting value. A trapped component obstructs this particular descent argument.

## A common algebraic construction

Suppose a regular pair satisfies (1) and also

$$AB=BA,\qquad AA^{\mathsf T}+BB^{\mathsf T}=tI+(t-2)J. \tag{3}$$

For $i\in[b]$ take $u_i=B^{\mathsf T}e_i$, $v_i=A^{\mathsf T}e_i$. Both have size $k$ and (2) follows by transposing commutation. Their pairwise overlap is the corresponding off-diagonal entry of the second matrix in (3). The $b$ selectors are distinct since $2k>t-2$ and form a full $b$-clique. Assembly gives $H(4t)$ directly. Circulant square matrices commute and are normal, so for such pairs (1) implies (3). The unrestricted graph allows independent row labels and requires only (1). A proof using (3) has to supply a single labelled representative satisfying both identities.

## Rounding bands and the last missing direction

Let $P_j(t)$ denote the existential, capacity-feasible prefix in [Rounding.lean](../Rounding.lean). Its witness is one joint $(Y,X)$. For a row already containing $d_r$ ones in $X$, its deficit $u_r=k-d_r$ must satisfy $0\le u_r\le s=b-j$. On each such prefix $u_r/s$ satisfies every next-column count over the rationals while $s>0$. At $j\le k$, capacity holds automatically for any valid marginal and mixed prefix, because $0\le d_r\le j\le k$ and $s\ge t$. In passing from width $j$ to $j+1$, a deficit of zero forces the new bit to zero and a deficit of $s$ forces it to one. Given all count equations, these boundary conditions are exactly what preserves capacity.

Set $a=\min(k,h-1)$. The disjoint bands of steps $P_j(t)\Rightarrow P_{j+1}(t)$ are $j=0$, $1\le j<a$, $a\le j<h-1$ and $j=h-1$. Empty bands are valid. The second band ends at a width at most $k$. In all four implications the output witness can replace the input witness. R gives $P_0$, induction reaches $P_h$, and the bordering theorem followed by seven-column completion gives $H(4t)$. Conversely a square witness supplies every $P_j$ up to $h$. This equivalence locates the full difficulty in proving the steps uniformly.

At $j=h-1$ the assembled matrix $C$ has $n-8$ mutually orthogonal columns. For **any** such real sign matrix, the rational kernel of $C^{\mathsf T}$ has dimension eight. Compute a rational basis $Q\in\mathbb Q^{n\times8}$ and take eight row indices $I$ for which $Q_I$ is invertible. Put $L=Q Q_I^{-1}$. Any extending sign vector must have the form $L\sigma$ with $\sigma\in\{\pm1\}^8$, and it extends exactly when every entry of $L\sigma$ is a sign. The two opposite vectors have the same test result, giving at most **128** tests. For $C$ coming from the bordered construction, its outside columns sum to $2t(e_1-e_2)$ by the known row sizes of $Y$. Any extending vector therefore has its first two entries equal and can be oriented to start $(+,+)$.

There is a short certificate that the 128 tests fail for a *specified* $C$. For each row $\ell$ of $L$, expand $(\ell\cdot\sigma)^2-1$ in the 29 coordinates $(1,(\sigma_i\sigma_j)_{i<j})$. Choose a basis of the space of these rational coefficient rows. It has at most 29 members. It suffices to test these rows on the 128 sign patterns. Verifying $C^{\mathsf T}Q=0$, rank eight, $L_I=I_8$, and the rational row span makes the result independently replayable. The choices of $C$ and $L$ vary with $t$.

Thus a way to prove the last band is to show that whenever $P_{h-1}(t)$ exists, **some** admissible width-$(h-1)$ prefix gives an accepting pattern. Its original columns plus that pattern reach $n-7$. Completion, followed by extraction, gives $P_h(t)$ with all capacities. We do not need to assume in advance that the new column respects capacities. A rejecting prefix gives no exclusion of a different prefix or order.

## Finite row types at defect eight

For $n\equiv0\bmod4$ let $K=nI-CC^{\mathsf T}$. Since $C^{\mathsf T}C=nI$, $K/n$ is the orthogonal projector onto $\ker C^{\mathsf T}$. Thus $K$ is integral, has rank eight, has diagonal 8 and satisfies $K^2=nK$. Its off-diagonal entries are even, since each is a sum of $n-8$ signs. Positive semidefiniteness gives $|K_{ij}|\le8$. Choose eight independent coordinates $I$ and set $G=K_{I,I}$. This matrix is positive definite, so each off-diagonal entry is in $\{-6,-4,-2,0,2,4,6\}$.

Every row type $r=K_{i,I}$ is one of the $9^8$ vectors in $\{-8,-6,\ldots,8\}^8$. The rank-eight Gram factorization gives $K=K_{:,I}G^{-1}K_{I,:}$, whence $rG^{-1}r^{\mathsf T}=8$. The matrix $L=K_{:,I}G^{-1}$ is the same coordinate interpolator as above. If $m_r$ is the number of rows of type $r$, then

$$\sum_r m_r=n,\qquad \sum_r m_r r^{\mathsf T}r=nG.$$

The second identity is the $I,I$ submatrix of $K^2=nK$. For each fixed $G$, the represented types with $m_r>0$ determine exactly which sign patterns survive. This gives finitely many possible terminal tests independent of $n$. The multiplicities, realizability by a sign prefix, and existence of a suitable prefix at each $t$ still require separate arguments.

There are two rank bounds on the quadratic tests. With $\ell=rG^{-1}$ one has $\ell G\ell^{\mathsf T}=8$. As $G_{ii}=8$, every test-coefficient row

$$c_\ell=(\|\ell\|^2-1,(2\ell_i\ell_j)_{i<j})$$

annihilates $(1,(G_{ij}/8)_{i<j})$. Hence at most **28** independent rows suffice for these sign prefixes. If one pattern accepts, Verheiden completes the remaining seven columns. The eight independent completing sign columns give eight independent pivot patterns $\sigma_1,\ldots,\sigma_8$ since restriction to $I$ is an isomorphism on the kernel. The eight lifted vectors $(1,(\sigma_{ai}\sigma_{aj})_{i<j})$ are independent as well. A linear relation among them would give $\sum_a\lambda_a\sigma_a\sigma_a^{\mathsf T}=0$; conjugating by the inverse of the matrix with those eight columns forces every $\lambda_a=0$. Each lifted vector annihilates every $c_\ell$, so an accepting prefix has **rank at most 21**. Rank $22$ through $28$ is a sufficient obstruction for a fixed prefix. Rank at most 21 can also occur for rejecting prefixes. For example the order-12 control has rank 4 and no accepting pattern. [Exact endgame controls](verify_endgame.py)

There is also a common-factor test. For a completed square let $T$ be its eight added sign columns. Then $TT^{\mathsf T}=K$. Hence $S=T_I$ is an invertible $8\times8$ sign matrix with $SS^{\mathsf T}=G$, and every realized type belongs to $\{zS^{\mathsf T}:z\in\{\pm1\}^8\}$. Conversely suppose **one** such factor $S$ supports every realized type. Taking $T=K_{:,I}G^{-1}S$ gives the requisite signs. Indeed a type $zS^{\mathsf T}$ interpolates to $z$, $C^{\mathsf T}T=0$, and $T^{\mathsf T}T=nS^{\mathsf T}G^{-1}S=nI$. Thus there is full completion exactly in this case. The columns of $S$ can be chosen as eight distinct members of the 128 oriented representatives up to independent column signs. In particular, more than 256 distinct realized row types, or more than 128 classes modulo $r\sim-r$, rule out a particular prefix. An obstruction to one sign factor has to cover all other factors before it excludes that prefix.

## One-column replacement

Given $n-8$ mutually orthogonal columns, delete one and retain the other $n-9$. On the resulting nine-dimensional kernel the same rational coordinate argument enumerates at most $2^{9-1}=256$ possible sign vectors up to negation. Look for a pair with full scalar product zero. Every possible replacement of the deleted column by two new orthogonal columns over the retained prefix occurs in this test. A successful pair reaches $n-7$, so the published theorem completes the square. After a successful replacement it is legitimate to re-extract a fresh admissible incidence prefix. A negative result on every deletion concerns this local set of replacements.

## Unrestricted disproof and the finite-cutoff alternative

For $t\ge2$, put $v=4t-1$ and $w=2t-1$. The square existence statement is equivalent to decomposing the edges of the multigraph $(t-1)K_v$ into copies of $K_w$. In a normalized square remove the first row and column and retain the plus supports in the remaining rows. Each has $w$ points and each point pair occurs $t-1$ times. Conversely in such a decomposition, counting pairs through a point gives degree $(v-1)(t-1)/(w-1)=w$. Counting incidences gives exactly $v$ blocks. Add a positive first row and first column and sign-encode the blocks. All other columns have $2t$ pluses and overlap at $t$ pluses, so all are orthogonal. Multiplicities may be allowed on input. The resulting square has orthogonal rows as well.

A negative answer may therefore specify one integer $t$ and exclude all such decompositions by a proof or a complete, replayable unrestricted exhaustion. For a Boolean encoding one may instead use a labelled $v\times v$ matrix of incidence bits with row weight $w$, column weight $w$ and every pair of columns meeting $t-1$ times. Every solution decodes and every normalized square encodes. Fixing any further symmetry requires a proof that each possible square has a surviving representative. If there is a counterexample, repeatedly stripping factors of two from its multiplier gives one in $D$ by the contrapositive of doubling and the covered-order constructions.

A positive proof may also give an explicit integer $T$ with a uniform theorem for **all** $t\in D$ above $T$, and matrices or proofs covering **all** members up to that *same* $T$. These form a dependent pair. The identity of the certified cutoff must travel with the finite results. A list of known orders, including a filled order 2396, can enter this argument only after the parameter match and completeness of the finite coverage have been verified.
