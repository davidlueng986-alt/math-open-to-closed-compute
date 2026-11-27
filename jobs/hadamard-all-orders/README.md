# A proof map for the full Hadamard conjecture

Let $H(n)$ mean that $n$ mutually orthogonal sign columns of length $n$ exist, and let $P(n,k)$ mean that $k$ such columns exist. The target is $H(4t)$ for **every** positive integer $t$. This file gives two exact sets of proof obligations. The shorter one has **two open families**. Construct a residual design, then prove an integral extension step for compatible prefixes of that design. Both families are necessary and together they are sufficient, given the published completion theorem. The fractional extension problem already has an explicit solution at every step.

**全題仲未攻克。** 以下每條未證引理都寫明要覆蓋邊啲 $t$、可以更換邊啲已選嘅集合，以及點樣接返去全猜想。單獨做好幾多個階數，量度唔到距離通證仲有幾遠。

The current closure DAG adds an exact pivot-pair formulation, the defect-eight row types, and ready-to-hand-off tasks for both possible answers. [Closure DAG](closure-dag/README.md) · [Research task list](closure-dag/TASKS.md)

## What is known about the distance

Write $r(n)=\max\{k:P(n,k)\}$. Unconditionally, for every $\epsilon>0$ and all sufficiently large multiples of four, $r(n)\ge n/2-O_\epsilon(n^{113/132+\epsilon})$. In particular the literature guarantees $(1/2-o(1))n$ orthogonal columns. Verheiden proved that **any** $n-7$ real orthogonal sign columns of length $n$ can be completed to $n$ for the orders used here. The conjecture follows if that threshold can be reached for every required $n$. The lower bound gives neither a rate of proof progress nor an effective finite search for the rest. [Graham–Shparlinski, §3](https://arxiv.org/abs/0709.2704) · [de Launey–Levin, Theorem A](https://arxiv.org/abs/1003.4003) · [Verheiden, thesis §4](https://thesis.caltech.edu/2899/) · [Verheiden, journal article](https://doi.org/10.1016/0097-3165(80)90028-X)

At $n=2396$, the verifier constructs **1,196 orthogonal columns** and checks all **714,610** pairwise inner products exactly. The seven-column completion theorem would apply at **2,389**. Extension may require changing the previously chosen columns. In the separate cyclic construction, 310 of 598 shift pairs vanish on one witness and 49 further original equations suffice under its documented constraints. Neither count measures $r(2396)$. This order remains the smallest gap in the cited frontier. [Explicit construction](verify.py) · [Cyclic certificates](../hadamard-2396-coverage/README.md) · [Frontier snapshot](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/FRONTIER.md)

## Dependency table

| ID | Statement to establish | Status |
| --- | --- | --- |
| 1 | $H(n)\Rightarrow H(2n)$. Strip powers of two from $t$. | Lean |
| 2 | Paley handles odd $t$ when $4t-1$ or $2t-1$ is a prime power, including $t=1,3$. Scarpis–Đoković handles $4t=q(q+1)$ for prime powers $q\equiv3\bmod4$. | Published |
| 3 | Normalize a square witness and extract the two incidence families below. | Proved below |
| 4 | For every remaining $t$, choose $4t-2$ blocks of size $t$ on $2t$ points so every point pair occurs $t-1$ times. This is obligation **R**. | **Open in this route** |
| 5 | Pair counts in R force all point degrees and the total number of blocks. The symmetric fractional block selection satisfies every equation. | Proved below |
| 6 | In any such design, each equal partition of the points has squared row imbalances summing to $2t^2$. For odd $t\ge3$ at most one block can be an entire half. | Lean |
| 7 | Start with the empty inner family. Its row capacities hold. | Lean |
| 8 | At every admissible prefix, the remaining row capacities give an explicit fractional next column satisfying **all** old intersections. | Lean |
| 9 | A fractional next column exists with at most $2t+j$ fractional positions after $j$ inner columns. | Linear algebra below |
| 10 | For each required $t$ and $0\le j<2t-8$, existence of an admissible prefix of width $j$ implies existence at $j+1$. This is integral obligation **B**. | **Open in this route** |
| 11 | For any candidate of the right size, the last of its $2t$ outside-point equations follows from the preceding $2t-1$. | Lean |
| 12 | The bordered incidence matrix has $1+2t+j$ mutually orthogonal sign columns. | Lean |
| 13 | Set $j=2t-8$ and apply seven-column completion. Alternatively $j=2t-1$ gives a full matrix directly. | Lean for the assembly, published for completion |
| 14 | Induction on $j$, then doubling, deduces the full conjecture from R and B. | Lean, conditional on the two open families and the cited results |

Let $D$ contain all odd $t\ge5$ missed by the three substitutions in row 2. Obligations R and B run over **every** $t\in D$. Other proved constructions may be added to the covered cases. The remaining set is infinite. For $t=599+100590k$, $k\ge0$, the integer $4t-1$ is divisible by both 5 and 479, and $2t-1$ by both 3 and 7. Only $O(\sqrt T)$ integers $t\le T$ can have $4t=q(q+1)$, while this progression has positive density. At $t=599$ the factorizations are $2395=5\cdot479$ and $1197=3^2\cdot7\cdot19$, and $16t+1=9585$ lies strictly between $97^2$ and $98^2$. [Paley (1933)](https://doi.org/10.1002/sapm1933121311) · [Đoković, Theorem 1](https://arxiv.org/abs/1601.00635)

**One infinite branch already closes.** Set $q=43^{60k+1}$ and $t=q(q+1)/4$ for $k\ge0$. Then $q\equiv43\pmod{226920}$ with $226920=8\cdot3\cdot5\cdot31\cdot61$. Thus $t$ is odd, $4t-1$ is divisible by 31 and 61, and $2t-1$ is divisible by 3 and 5. Both direct Paley tests miss every member. Applying Paley to $q+1$ and then Scarpis–Đoković gives a full $H(q(q+1))$ for **every** $k$. The modular identity is checked in Lean. Python reconstructs the first member, $H(1892)$, and checks all 1,788,886 pairwise products. This branch is an application of published constructions. [Lean congruence](Constructions.lean) · [Matrix reconstruction](verify.py) · [Đoković’s construction](https://arxiv.org/abs/1601.00635)

## The construction and its converse

Put $n=4t$, $m=4t-2$, $b=2t-1$ and $h=2t-8$. The common ground set for **columns** of the incidence matrices below has $m$ row labels. In the equivalent block-design description a row of $Y$ is a block on $2t$ points.

| Conditions on the same row labels | Exact targets |
| --- | --- |
| Outside matrix $Y$ with $2t$ columns | Each row has $t$ ones. Each column has $2t-1$ ones. Each pair of columns meets in $t-1$ rows. |
| Inside matrix $X$ with $j$ columns | Each column has $2t-2$ ones. Each pair meets in $t-2$ rows. |
| Between $Y$ and $X$ | Every outside column meets every inside column in $t-1$ rows. |

**Extraction.** Given a full square Hadamard matrix, flip column and row signs to make the first row and column positive. All other rows and columns are balanced. Separate the nonconstant columns by the second row. Exactly $2t$ have a minus, and $b$ have a plus. Delete the first two rows and encode plus as one. Call the resulting groups $Y$ and $X$. Two balanced orthogonal sign columns have exactly $t$ common positive entries. Subtract the contribution of the top two positions to get the table. For each lower row, its scalar products with the first and second rows both vanish. Subtracting the equations gives zero sign sum across its $2t$ outside positions, hence exactly $t$ ones there. The other $b$ positions then contain $t-1$ ones. This last fact supplies the capacities used below.

**Assembly.** Conversely, append two signs at the top of each incidence column. Append $(+,-)$ to $Y$ and $(+,+)$ to $X$, and add one constant positive column. Each nonconstant column has $2t$ plus signs and each pair has $t$ simultaneous plus signs. For positive supports $U,V$, the inner product is $n-2(|U|+|V|)+4|U\cap V|$, hence every off-diagonal inner product vanishes. This proves $P(4t,1+2t+j)$, with $1+2t+h=4t-7$. Conversely any full witness supplies every prefix by taking any $j$ of its $b$ inside columns. No cyclic, circulant, or multiplier symmetry is required. [Lean assembly](Assembly.lean)

## R — choose the outside blocks

There is a finite, explicit system for each $t$. For every $t$-subset $S$ of the $2t$ points introduce a variable $w_S$. For each unordered pair $\{u,v\}$ require $\sum_{S\supseteq\{u,v\}}w_S=t-1$. A nonnegative integral solution gives R. Summing over $v\ne u$ gives degree $2t-1$ at $u$. Summing those degrees gives $4t-2$ blocks. The constant rational choice $w_S=(t-1)/\binom{2t-2}{t-2}$ meets every pair equation. For odd $t\ge3$ any integral solution also satisfies $w_S+w_{S^c}\le1$, as follows from the identity below. Thus one may use binary selection variables from the outset. A way to subdivide R is to enumerate the point pairs and prove feasibility after imposing each extra equality while retaining all earlier ones.

**An obstruction for odd multipliers.** Bisect the $2t$ points in any way. In row $r$ let $a_r,b_r$ count its points on the two sides. Each of the $t^2$ cross pairs occurs $t-1$ times, so $\sum_r a_rb_r=t^2(t-1)$. Using $a_r+b_r=t$ and $m=4t-2$ gives

$$\sum_{r=1}^{4t-2}(a_r-b_r)^2=2t^2.$$

For odd $t$, every summand is positive. A row equal to either entire half contributes $t^2$. Two such rows would exhaust the sum and leave other positive terms. In particular no two rows of $Y$ are equal or complementary. At a prime $t=p\ge5$, this rules out invariance under a point permutation consisting of two $p$-cycles. Only the cycles themselves could be fixed blocks, so there is at most one. All other block orbits have size $p$, whereas the number of fixed blocks must be $4p-2\equiv p-2\pmod p$. This eliminates that proposed symmetry also at $p=599$. [Lean energy and pure-block bound](OuterEnergy.lean)

## B — round the next column

Suppose $Y$ and $j$ inside columns satisfy the table. For a lower row $r$, write $d_r$ for its current number of inside ones, $u_r=t-1-d_r$ for how many ones it still needs, and $s=b-j$ for remaining inside slots. Call the prefix **admissible** if $0\le u_r\le s$ for every row. All prefixes of a full matrix are admissible. At $j=0$ every $Y$ supplies an admissible prefix.

The next binary column $z$ has to pick $2t-2$ rows. It must pick $t-1$ rows in each $Y_i$ and $t-2$ rows in each previous $X_i$. Where $u_r=0$ it must pick zero, and where $u_r=s$ it must pick one. Those boundary conditions suffice to preserve capacity after an integral step. **For any admissible prefix with $s>0$, $z_r=u_r/s$ solves every one of these equations over the rationals.** The three counts, before division, are

$$\sum_r u_r=s(2t-2),\qquad \sum_{r\in Y_i}u_r=s(t-1),\qquad \sum_{r\in X_i}u_r=s(t-2).$$

For the last identity, the previous columns contribute $(2t-2)+(j-1)(t-2)$ to $\sum_{r\in X_i}d_r$. For the middle identity they contribute $j(t-1)$. For the total they contribute $j(2t-2)$. This proves all three. Also $\sum_i |z\cap Y_i|=t|z|$ for a binary column, so one outside equation is redundant. [Lean fractional extension](Rounding.lean) · [Lean redundant equation](Constructions.lean)

**How far fractional rounding goes.** The equality matrix has at most $2t+j$ independent rows because the outside incidence rows sum to $t$ times the size equation. If more than $2t+j$ coordinates are strictly fractional, there is a nonzero rational null vector supported there. Move in that direction to the first box boundary. This keeps all equations and all previously integral positions. Repeating gives the bound in row 9 of the table. The last fractional entries can be genuinely coupled. For a Paley order-20 example the first-step polytope has a vertex with eight fractional entries. Eight independent count equations on these eight positions have minor determinant 12. The other ten entries are fixed at their bounds, so this point is a vertex. The same $Y$ has an integral solution. Thus choosing an arbitrary LP vertex does not settle B. [Exact vertex and determinant](verify.py)

**The remaining quantifier.** For every $t\in D$ and $0\le j<h$, prove that *if some admissible prefix of width $j$ exists, some admissible prefix of width $j+1$ exists*. One may replace both $Y$ and the earlier $X$ columns between steps. Proving integral rounding for every presented prefix would suffice too, but existence needs only a suitable choice. The first open rounding target is particularly concrete. Choose $2t-2$ blocks of a suitable $Y$ so every point occurs in exactly $t-1$ chosen blocks. At $t=599$ this asks for 1,196 of 2,394 blocks covering each of 1,198 points 598 times. Later columns must additionally meet every earlier selection in exactly 597 blocks. A construction for this first step on an explicitly described infinite subfamily of $D$ would advance the all-order route. [Lean implication from R and B](Rounding.lean)

## Finer proof obligations with separate marginals

This equivalent variant lets one work on inside intersections before proving all the mixed counts. Put $a=\min(t,h)$.

1. Given $Y$, fix one row and choose $a$ outside columns incident with it. Clear that row in the selected columns. Every selected size and every pair intersection drop by one. These columns satisfy the inside marginal up to width $a$. [Lean seed](Reductions.lean)
2. For $a\le j<h$, prove that existence of an inside marginal of width $j$ implies existence at $j+1$. Replacing an earlier marginal is allowed. At $t=599$ this gives 591 separate growth steps.
3. Retain a **full width-$h$** inside marginal and a full $Y$. Let a stage $(j,\ell)$ mean that all mixed counts of the first $j$ inside columns hold, and the next inside column agrees with the first $\ell$ outside columns. Prove existence at $(j,\ell+1)$ from existence at $(j,\ell)$ for $\ell<2t-1$. Each step adds one equality and preserves the entire earlier set of equalities on a common witness. The final outside equality follows from row sizes. At $t=599$ this gives $1190\cdot1197=1{,}424{,}430$ single-equality steps, indexed by the same two variables for all $t$. [Lean stage theorem and three-family implication](Constructions.lean)

The compatibility condition has mathematical content. At order 20, swapping just two lower row labels in $X$ preserves both marginals and breaks eight mixed counts. Greedy extension can also fail for general partial matrices at arbitrarily large orders. Repeat every row of $H(4)$ exactly $t$ times to give four orthogonal columns of length $4t$. If a fifth column were orthogonal to these four, the four sums on the repeated row groups would form a vector in the kernel of $H(4)^{\mathsf T}$. All four sums would have to vanish, which is impossible when $t$ is odd. [Marginal permutation check](verify.py)

## Reproduction and proof boundary

Run `python3 jobs/hadamard-all-orders/verify.py` from the repository root. Python uses only the standard library. Orders 20, 44 and 60 exercise extraction, reconstruction, capacities and the fractional certificate through **every** prefix of the known solutions. For order 20 the checker also goes through all 252 choices of the first half of an equal cut of the outside points.

For the $2396\times1196$ witness, the upper block is a full matrix of order $1196=4\cdot13\cdot23$. A length-13 ternary quadruple and a symmetric length-23 Williamson quadruple give four length-299 sign words. Their summed periodic autocorrelation vanishes at every nonzero shift, as the checker verifies before building the Goethals–Seidel array. The lower block consists of 1,196 columns of the order-1,200 Sylvester double of Paley $H(600)$. Stacking corresponding columns preserves zero inner products. Both source squares and **every** pair of stacked columns are independently checked. The construction uses known ingredients and supplies a reproducible lower bound at this order. [Williamson data, pinned SageMath table](https://github.com/sagemath/sage/blob/8de8dad7bcb38e1baa43508cbe944bf04a2d0401/src/sage/combinat/matrices/hadamard_matrix.py#L636) · [Goethals–Seidel array](https://github.com/sagemath/sage/blob/8de8dad7bcb38e1baa43508cbe944bf04a2d0401/src/sage/combinat/matrices/hadamard_matrix.py#L1020) · [Checker](verify.py)

The GitHub workflow builds the Lean files with version 4.36.0 and treats warnings as errors. The two global implication theorems expose Paley-covered cases and Verheiden completion as inputs. R, B and their alternative marginal growth assumptions remain explicit hypotheses. The fractional identities, conditional induction, row-energy obstruction, doubling, and assembly have kernel-checked proofs. The converse via normalization, sparse rounding argument, and prime-cycle corollary have written proofs above. [GitHub Actions](../../.github/workflows/hadamard-all-orders.yml)
