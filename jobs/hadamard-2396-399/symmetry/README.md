# Automorphisms of abelian Legendre pairs of order 1197

Let $A,B:G\to\{\pm1\}$ both sum to 1, with combined periodic autocorrelation −2 at each nonidentity element of an abelian group of order 1197. The group $H$ of automorphisms fixing both functions has **order dividing 9**, for both possible group laws. The proof uses the previously archived exhaustive computation on the cyclic quotient of order 399. [Cyclic case and determinant argument](../../hadamard-2396-diagonal/multipliers.md) · [Finite 399-point exclusion](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/d9a5be164a58c45cb608e0272f1493c126ec82b1/runs/hadamard-2396-projections/45298481173/results.json)

## Passing to the elementary-3 group

Take $G=V\times C_7\times C_{19}$ with $V=\mathbb F_3^2$. Any automorphism preserves these primary factors. For any quotient map $\lambda:G\to C_q$ with $q=3,7,19$, no element of $H$ can satisfy $\lambda\circ h=-\lambda$. Indeed both projected words would be even on $C_q$. Their circulant matrices restricted to the even zero-sum lattice commute and satisfy $M^2+N^2=2396I$. Taking the determinant of $M+iN$ gives $a^2+b^2=2396^{(q-1)/2}$. The prime 599 is 3 modulo 4 and appears to an odd power here. Every nonzero sum of two integer squares has even valuation at 599. This contradiction applies to every choice of $\lambda$.

Consequently the images at 7 and 19 lie in the quadratic residues. Any nonidentity involution in $\mathrm{GL}(2,3)$ has a −1 eigenvector on the dual. Its occurrence in the image on $V$ would give a forbidden $\lambda$. By Cauchy's theorem the image has odd order. Since $|\mathrm{GL}(2,3)|=48$, it has order 1 or 3. In the second case a generator is unipotent with fixed line $L$ and acts trivially on $V/L$.

In suitable coordinates a generator acts as $(x,y)\mapsto(x+y,y)$. If a **pure** shear fixing the other two factors fixes even one sign word, consider the horizontal shift $(1,0)$. On each plane the rows $y=1,2$ of that word are constant, contributing 3 each. The row $y=0$ and the three rows of the other word contribute at least −1 each, for a combined lower bound of 2. Across 133 planes this gives at least 266. Thus the projection from $H$ to $\mathrm{QR}_7\times\mathrm{QR}_{19}$ has trivial kernel. More generally, on $\mathbb F_p^2\times K$ the corresponding bound is $2|K|$ for every odd prime $p$. On each plane $p-1$ cycles contribute $p$ each and the other $p+1$ cycles contribute at least $2-p$ each. [Lean proof for every number of 3-by-3 planes and the dual involution check](../Obstructions.lean)

The image therefore has order dividing 27. If it had order 27 it would contain all independent square multipliers on 7 and 19. Quotient by $L$ on the 3-factor, choosing any line if the image there is trivial. The quotient is $C_3\times C_7\times C_{19}\cong C_{399}$, its two projections have entries in $\{\pm1,\pm3\}$, and both would be invariant under those independent squares. The archived 399-point census excludes every such pair having the required projected autocorrelations. Thus $|H|$ divides 9. Common automorphisms carrying the two negative supports to separate translates are covered by centring each support. Its cardinality 598 is coprime to 1197, so its sum in $G$ determines a unique centring translation. The result concerns simultaneous automorphisms of abelian Legendre pairs. Other Hadamard constructions have their own symmetries.

## A seven-entry reduction for the pure order-nine action on 19

In the cyclic group write a position as $(x,k)\in C_{63}\times C_{19}$. Suppose the full square group acts on $k$ and fixes $x$. A word has signs $a_x,b_x,c_x$ over $k=0$, nonzero squares, and nonsquares respectively. Write $M=(b+c)/2$ and $D=(b-c)/2$. At each $x$ precisely one of $M,D$ is nonzero. The 63-point projection is $X=a+18M$. Call $M_x\ne0$ a heavy position. All unindexed sums in this section include both words.

Put $W=\sum M^2$ and $J=\sum aM$. The required zero-shift identity is $2358=126+36J+324W$, so $18W+2J=124$. Since $|J|\le W$, integrality gives **$W=7$ and $J=-1$**. There are three entries of $X$ of magnitude 19, four of magnitude 17, and 119 of magnitude 1. For a factor of any odd prime order $p$ with full square invariance, the same expansion at length $mp$ gives $(p-1)W+2J=2(m-1)$. A related large-entry norm argument appears in the Spence search at order 2396. [Kumar's search notes, §92](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/search/NOTES.md)

For $t\ne0$ let $H(t)=\sum M_xM_{x+t}$, $L(t)=\sum a_xa_{x+t}$ and $K(t)=\sum(a_xM_{x+t}+M_xa_{x+t})$. The equation for $X$ is
$$324H(t)+18K(t)+L(t)=-38.$$
Clearly $|K|\le14$. Write $z_f=\sum_x M_{f,x}$ for each word. The singleton sign sums are $1-18z_f$. Since $z_A-z_B$ is odd, the sum of their absolute values is at least 18. At any shift there are at least as many agreeing positions as the absolute sign sum in a word. Thus $-90\le L\le126$. These bounds force **$H(t)\in\{0,-1\}$**. For a shift with $H(t)=-1$ the even integer $K(t)$ must be 10, 12, or 14. If $h$ of the 31 shifts up to reflection have value −1, then $z_A^2+z_B^2=7-2h$. The only possibilities are $h=1$ and $h=3$. [Kernel-checked arithmetic steps](../Obstructions.lean)

Support intersections determine $H(t)$ modulo two. The program takes the larger support, of size 4 to 7, up to simultaneous affine automorphisms of $C_{63}$. It independently translates the smaller support. It fixes one nonzero sign in each nonempty row while enumerating, then restores all row orientations before the quotient tests. These operations give a cover and can leave equivalent templates. A second program checks the larger support orbit counts using Burnside's lemma and directly sums all 31 correlations for every emitted signed pair. [Enumerator](templates.cpp) · [Independent orbit and correlation check](check_templates.py) · [Signed templates](../../hadamard-2396-squares/templates.txt)

| Larger support size | Affine support orbits | Signed templates | Templates surviving the quotient tests |
| ---: | ---: | ---: | ---: |
| 4 | 312 | 2,804 | 2,773 |
| 5 | 3,223 | 977 | 957 |
| 6 | 30,428 | 15 | 13 |
| 7 | 245,009 | 46 | 20 |
| Total | | 3,842 | 3,763 |

For $d_f=\sum_x D_{f,x}$ the length-19 zero-shift equation reads $\sum_f[(1-18z_f)^2+18(z_f^2+d_f^2)]=2270$. Thus $d_A^2+d_B^2=126+2(z_A+z_B)-19(z_A^2+z_B^2)$, with each $d_f$ congruent to the number of light positions in its row modulo two. There are 8,679 allowed orientations. For each $q=3,7,9$ we enumerate the possible projections of $X$ by adding an odd integer between $-63/q$ and $63/q$ in each bin to $18M_q$. We require sum 1 per row and all quotient autocorrelations. Taken together the tests leave 8,521 orientations in 3,763 templates. The tests permit separate completions on different quotients. [Quotient enumerator](quotients.cpp) · [Orientation and sieve driver](sieve.py) · [Exact output](expected.txt)

## The coupled 57-point test

A nontrivial character of $C_{19}$ of quadratic sign $\chi$ evaluates a vertical column to $F+i\sqrt{19}\chi D$, where $F=a-M$. This follows from the quadratic Gauss sum for 19. On the length-three horizontal quotient write $X,F,D$ also for the compressed rows. An exact pair requires the sums over both words of the following four scalars to be $1598,2396,2396,0$, in order.

1. $\|X\|^2$.
2. $\|F\|^2+19\|D\|^2$.
3. $(\sum F)^2+19(\sum D)^2$.
4. $\sum_i F_i(D_{i+1}-D_{i-1})$.

These scalars give all 57-point correlations because each real even function on $C_3$ is determined by its value at zero and its total, and its odd part has one independent entry. Each singleton bin sums 21 signs and each $D_i$ sums the light positions in that bin. Reversing the sign of $D$ reverses the fourth scalar while preserving the other three. The implementation matches absolute fourth scalars and complementary totals. All 89 projected template pairs pass. This records a boundary of this particular quotient test. [Exact 57-point computation](vertical.cpp)
