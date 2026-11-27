# The first binary column in the Hadamard closure DAG

**One finite task is complete.** The two order-44 signature tables have exactly 21 common entries. For the all-order task we prove a condition on a given outside design that constructs a first column compatible with every other legal first column. We also obtain a full square on the infinite family $4t=2(45^{12j+1}+1)$, $j\ge0$, by applying published conference-matrix constructions. Every member belongs to the original remainder $D$ of this project. The family and the single-column criterion leave other orders open. [Task cards](../closure-dag/TASKS.md) · [All-order reduction](../README.md)

## A signed solution at every order

Let $t\ge2$, $k=t-1$, $b=2t-1$ and $m=2b$. An outside design is an $m\times 2t$ binary incidence matrix $Y$ with $t$ points per row, degree $b$ per point and codegree $k$ per distinct pair of points. Write $R_i$ for row $i$, $J$ for an all-ones matrix and $G=YY^{\mathsf T}-tI$. A legal first column is $x\in\{0,1\}^m$ with $Y^{\mathsf T}x=k\mathbf1$. Summing the point equations gives $\mathbf1^{\mathsf T}x=2k$. Two different first columns are compatible if their intersection is $t-2$.

Since $Y^{\mathsf T}Y=tI+kJ$, we have $Y^{\mathsf T}G=ktJ$ and $G\mathbf1=2tk\mathbf1$. For **any** $c\in\mathbb Z^m$ with $\mathbf1^{\mathsf T}c=2$, put

$$Z(c)=Gc-k\mathbf1.$$

Then $Y^{\mathsf T}Z(c)=k\mathbf1$ and $\mathbf1^{\mathsf T}Z(c)=2k$. In particular $c=2e_p$ works at every chosen row $p$. Its entry at $p$ is $-k$. There is even an integral unit-count vector $w=b\mathbf1-4Ge_p$ because $b^2-4tk=1$. Its coordinate sum is two. This eliminates every linear congruence obstruction to the signed first-step equations, including congruences on their total. Finding a vector inside the binary box is the remaining issue. [Lean signed lattice witnesses](Lattice.lean) · [Lean general coefficients](PairDefect.lean)

## A certificate compatible with every other column

For any legal first column $x$, $Gx=kt\mathbf1-tx$. Hence

$$\langle Z(c),x\rangle=2k-t\langle c,x\rangle.$$

If $Z(c)$ is binary and differs from $x$, their intersection lies in $[0,2k-1]$ and is $2k$ modulo $t$. The unique possible value is **$t-2$**. Thus each distinct binary $Z(c)$ is adjacent to every other vertex of the fixed design's compatibility graph. Collecting $h=2t-8$ different such columns on one $Y$ when $t\ge5$ already gives $4t-7$ orthogonal sign columns and hence a full square by Verheiden. Equality of coefficient vectors is unnecessary. It is their binary images that must be distinct. The proof only needs integral coefficients in the displayed congruence. General feasible $x$ always has the rational representation $x=Z((\mathbf1-x)/t)$. [Lean overlap identity and universality](PairDefect.lean) · [Clique assembly and completion](../closure-dag/lemmas.md#signature)

For a particularly small certificate take $c=e_p+e_q$ with distinct rows and $\lambda=|R_p\cap R_q|$. Then

$$z_i=|R_i\cap R_p|+|R_i\cap R_q|-t(\mathbf1_{i=p}+\mathbf1_{i=q})-k,\qquad
\sum_i z_i(z_i-1)=2t(k-\lambda).$$

Indeed $z_p=z_q=\lambda-k$, and $Gz=kt\mathbf1-tz$ follows from the mixed counts. Taking the dot product of $z$ with $z-\mathbf1=G(e_p+e_q)-t\mathbf1$ yields the formula. Each summand is a nonnegative integer and vanishes exactly at 0 and 1. Distinct rows therefore intersect in at most $t-1$ points. At equality the formula produces a legal first column on this same $Y$, with both seed entries zero. Every other legal column then contains exactly one of $p,q$. All of these assertions hold also for even $t$. [Lean defect, binary certificate and capacity-feasible first prefix](PairDefect.lean)

## Several pairs at one point

Now suppose $t\ge5$ is odd. Call rows with intersection $t-1$ a near-twin pair. If the two blocks are $U\cup\{a\}$ and $U\cup\{b\}$, record the exchanged point pair $\{a,b\}$. Away from the two seed rows, the formula for $z_i$ reduces modulo two to the indicator of exactly one of $a,b$ in $R_i$, since $k$ is even. Its value on the two seed rows is zero.

The near-twin pairs are disjoint **as pairs of row indices**. If $q$ and $r$ were both near twins of $p$, the certificate from $p,q$ would have $z_r=|R_q\cap R_r|$. Their intersections with $R_p$ alone force $|R_q\cap R_r|\ge t-2>1$.

In particular, suppose a single point $a$ can be exchanged with $d$ different points $b_i$. This gives $d$ **distinct** universally compatible columns. On the two seed rows for $\{a,b_j\}$, the membership of $a$ changes, while that of $b_i$ is constant for $i\ne j$. Thus the certificate for $\{a,b_i\}$ picks exactly one of those rows, and the certificate for $\{a,b_j\}$ picks neither. A star of degree $d\ge 2t-8$ suffices for $H(4t)$. This test uses only the outside row intersections and the identities of the two exchanged points. [Threshold theorem](../closure-dag/lemmas.md#signature)

### When all exchanges share a point

A star of full degree $b$ exists if and only if a conference graph on $b$ points exists. Such a graph is a strongly regular graph of degree $k$, with $k/2-1$ common neighbors for adjacent points and $k/2$ for nonadjacent points.

For the forward implication the $b$ disjoint pairs use all $2b$ rows. Label the center $\infty$ and write the pair for $i$ as $S_i\cup\{\infty\},S_i\cup\{i\}$, with $|S_i|=k$ and $i\notin S_i$. Put $A_{ij}=\mathbf1_{j\in S_i}$. The outside codegree of $i,j$ is
$2(A^{\mathsf T}A)_{ij}+A_{ij}+A_{ji}=k$ for $i\ne j$. Its parity forces $A_{ij}=A_{ji}$. The remaining equation gives exactly the two common-neighbor counts. Conversely the neighbor sets of any such graph give the displayed block pairs. Their sizes, point degrees and point codegrees satisfy the outside requirements. The $b$ row-pair certificates then give all $b$ inner columns of a square. The equivalence between conference graphs and normalized symmetric conference matrices of order $b+1$ is classical. [Mathon, §1](https://doi.org/10.4153/CJM-1978-029-1)

**One missing exchange is forced.** If a star has at least $b-1$ neighbors, take $b-1$ pairs and call the missing point $e$. There are just two leftover rows. Exactly one contains the center by its point degree $b$. At each paired point $i$ the used rows contribute an odd degree, so the two leftover rows agree at $i$. At $e$ the used rows contribute an even degree, so the leftovers differ at $e$. Equal row sizes force an exchange of $\infty$ and $e$. This completes a full star.

At order **2396**, $t=599$, $b=1197$ and $h=1190$. A conference graph requires its vertex count to be a sum of two squares. Here $1197=3^2\cdot7\cdot19$ has primes congruent to 3 modulo 4 with odd exponent. Hence degrees 1196 and 1197 are impossible for this star. The six degrees **1190 through 1195** still meet the completion threshold if realized. General integer certificates and other Hadamard constructions are also available. [Published necessary condition, Theorem 1.1](https://doi.org/10.4153/CJM-1978-029-1) · [Arithmetic replay](verify_designs.py)

### The unpaired rows when the star misses at most seven points

Let $d=b-r$ for $1\le r\le7$, $I$ be the paired points, and $E$ the $r$ missing points. Remove the $d$ row pairs. Exactly $r$ residual rows contain the center and $r$ do not. For a finite point $j$ write its remaining incidence word as $(u_j,v_j)$ on these two groups. Let $s_j$ count the known sets $S_i$ containing $j$. From the codegree with the center and the total point degree,

$$|u_j|=k-s_j,\qquad |v_j|=|u_j|+\mathbf1_{j\in E}.$$

For $i,j\in I$ with $i\ne j$, let $A_{ij}=\mathbf1_{j\in S_i}$ and $w_i=(u_i,v_i)$. Reducing the pair codegree modulo two gives $(A+A^{\mathsf T})_{ij}=w_i\cdot w_j$ over $\mathbb F_2$. This also holds on the diagonal since each $w_i$ has even weight. The even-weight subspace in dimension $2r$ has radical spanned by the all-ones word. Hence the asymmetry matrix of the known $d\times d$ block has **binary rank at most $2r-2$**. Its entries depend on at most $\binom{2r}{r}/2$ classes of words, since a paired point has equally many ones in the two halves and complementary words have identical dot products with even words.

For $e\in E$, the words $w_e$ have odd weight and distinct ones are orthogonal modulo two. The paired rows contribute an even codegree to any two missing points. For **two missing points**, each exceptional word is either one lower singleton or both lower entries and one upper singleton. The two words must both be of the first type on different lower rows, or both of the second on different upper rows. A mixed pair has odd intersection. On the 1,195 paired points of a hypothetical star at order 2396, the rank bound is then two. The three complement classes are zero or all four, a matched upper/lower pair, and a crossed upper/lower pair. An asymmetric entry occurs exactly between the last two classes. At the other five candidate degrees the rank bounds are 4, 6, 8, 10 and 12. These restrictions give finite local data for a search even though the missing outside design has 2,394 rows. [Enumeration of residual word types and rank checks](verify_designs.py)

## An infinite subfamily inside D

Mathon's 45-vertex conference graph gives a symmetric conference matrix of order 46. Turyn's arbitrary-power theorem gives a symmetric conference matrix of order $45^e+1$ for every positive integer $e$. Its normalized core gives a conference graph on $v=45^e$ points. Set $b=v$ and $t=(v+1)/2$. The full-star construction above gives $H(4t)$, including explicit first-column selectors on that outside design. This combines published existence theorems with the row-pair construction. [Mathon, Theorems 1.3 and 4.1 and §5](https://doi.org/10.4153/CJM-1978-029-1) · [Turyn, On C-matrices of arbitrary powers](https://doi.org/10.4153/CJM-1971-056-0)

Choose $e=12j+1$, $j\ge0$. Then $t$ is odd since $45\equiv1\bmod4$. The first Paley parameter $2t-1=v$ is divisible by 3 and 5. The second, $4t-1=2v+1$, is divisible by 7 and 13 since $45^{12}\equiv1$ modulo each prime and $2\cdot45+1=91$. Neither parameter is a prime power. Finally $4t=2(v+1)\equiv1\bmod7$, whereas $q(q+1)$ modulo 7 takes only $0,2,5,6$. Thus Scarpis misses every member as well. These orders are unbounded and all lie inside the DAG's original $D$. The published theorems cover full squares throughout the progression. The executable matrix reconstruction here is at its first member. [Lean arithmetic](Coverage45.lean) · [Original coverage tests](../closure-dag/lemmas.md)

At **order 92** the replay constructs Mathon's graph in coordinates $(i,a,x)\in\mathbb Z_5\times\mathbb F_3^2$, checks all its degrees and pairwise common-neighbor counts, and builds the 90 blocks on 46 points. The 45 row pairs produce 45 distinct inner columns. The final independent sign-matrix test checks all $\binom{92}{2}=4186$ column pairs. [Executable construction](verify_designs.py) · [Mathon graph construction in SageMath](https://github.com/sagemath/sage/blob/8de8dad7bcb38e1baa43508cbe944bf04a2d0401/src/sage/graphs/generators/families.py#L4020)

## A fixed outside design that stops at one column

At **order 28**, three four-row switches on the recorded 26-block design take the exact number of legal first columns through **13, 13, 5, 1**. Each switch complements the four entries of every point occurring twice on those rows. The checker verifies all design equations at each stage. It exhausts all $\binom{13}{6}=1716$ selectors on each side of the pivot and joins equal integer signatures. The one remaining column selects lower rows $0,2,3,8,9,11,14,16,17,22,23,25$. It is also exactly the certificate from rows 12 and 13. Consequently this final design cannot support a two-column prefix, even though $H(28)$ exists. A proof using successive extensions must allow a change of outside design or impose an extra hypothesis on it. [Complete blocks, switches and exhaustive replay](verify_designs.py)

### A switch that preserves at least one old selector

There is also a sufficient condition for a paired switch on a **complete** input to retain an old first column. Use the pivot matrices $A,B$ and let $U,V$ be the two selector matrices of a full $b$-clique, with selectors as columns. The completed sign square gives $UV^{\mathsf T}=AB^{\mathsf T}$ by orthogonality between the two lower row groups. Indeed their sign inner product matrix simplifies to $4(UV^{\mathsf T}-AB^{\mathsf T})$ since all four matrices have row sums $k$. Inner row sums follow from orthogonality with the all-positive first row after normalization, equivalently the completed rows have $2t$ positive signs including the constant column and their $t$ outside entries.

Let $p=e_i-e_j$ select two finite points. Switch one alternating $2\times2$ submatrix in each half on these points, so $A'=A+w_Ap^{\mathsf T}$, $B'=B+w_Bp^{\mathsf T}$ with each $w$ a signed difference of the switched rows' unit vectors. Suppose the combined column Gram is preserved. Put $a=A^{\mathsf T}w_A$ and $b'=B^{\mathsf T}w_B$. Expanding the Gram gives $p u^{\mathsf T}+u p^{\mathsf T}=0$ for $u=a+b'+2p$, hence $u=0$. The alternating switch has $a\cdot p=-2$. Thus $a\cdot b'=4-\|a\|^2$ is even, as $a$ is a difference of two equal-weight binary rows. The ternary words $U^{\mathsf T}w_A,V^{\mathsf T}w_B$ each sum to zero and their dot product equals $a\cdot b'$. Two such ternary words of odd length and even dot product must agree somewhere. Otherwise every coordinate pair $(d,e)$ has $d+e+de$ odd, contradicting the three even sums. An agreeing coordinate means the same old selector has the same new signature on both sides. This argument concerns a single paired switch from a full clique. [Lean ternary parity step](SwitchParity.lean)

## Complete order-44 atlas

We use the normalized Paley-I matrix over $\mathbb F_{43}$, with bit 1 denoting $+1$, and pivot index zero in the outside family (original column 1). The first two original rows are the normalization rows. Within each pivot half, labels increase in the original row order. The JSON records the original point and row labels, the integer masks for all 21 shared signatures, and two decoded examples. Low bit 0 is the first row in the named half. [All labels and witnesses](atlas.json)

| Exact quantity | Paley $H(20)$ control | Paley $H(44)$ at pivot zero |
| --- | ---: | ---: |
| Subsets per half | 126 | 352,716 |
| First columns | 9 | 21 |
| Compatible unordered pairs | 36 | 210 |
| First columns outside the given square | 0 | 0 |

Each order-44 histogram has 352,716 distinct signatures, all with multiplicity one. Each uncompressed line contains 21 lowercase hexadecimal digits, a tab, the multiplicity and LF, in lexicographic order. Digit $i$ counts incidences in the $i$th finite-point column. The producer adds packed row words with zero carries. The independent verifier uses direct bit intersections for every archived line, proves both signature maps injective modulo 101 and solves all possible collisions with a modular inverse, then checks each exact integer witness. [A histogram](h44-a.tsv.xz) · [B histogram](h44-b.tsv.xz) · [Canonical SHA-256 digests](atlas.json) · [Independent verifier](verify_first_match.py)

From the repository root, run the following. The first two commands verify the committed results. The last one regenerates the two archives and the JSON.

~~~sh
python3 -B jobs/hadamard-all-orders/first-match/verify_designs.py
python3 -B jobs/hadamard-all-orders/first-match/verify_first_match.py
python3 -B jobs/hadamard-all-orders/first-match/atlas.py
~~~
