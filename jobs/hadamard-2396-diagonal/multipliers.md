# A common multiplier at length 1197 has group order at most 9

Let $A,B$ be a cyclic Legendre pair of length 1197 and let $H$ be a group of units modulo 1197 fixing both sign words. Then $|H|$ divides 9. The proof combines an elementary determinant obstruction with the existing finite exclusion on the 399-point quotient. It bounds this construction of a Hadamard matrix. [399-point computation and hypotheses](../hadamard-2396-projections/README.md#a-finite-exclusion-at-399) · [Archived enumeration of the eight cases](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/d9a5be164a58c45cb608e0272f1493c126ec82b1/runs/hadamard-2396-projections/45298481173/results.json)

## Even projections are impossible

Let $q$ be any of $3,7,19$, and compress each word by summing its coordinates modulo $q$. Denote the resulting integral vectors by $U,V$, and put $m=1197/q$. The two circulant convolution matrices $X,Y$ satisfy
$$
XX^T+YY^T=2396I-2mJ.
$$
Indeed, each entry of the left side sums the original two correlations over one residue class of shifts. Only the zero class includes the original zero-shift value 2394.

If the image of $H$ modulo $q$ has even order, it contains $-1$ because the multiplicative group modulo the prime $q$ is cyclic. Then $U,V$ are even functions and $X,Y$ are symmetric. Convolution by either preserves the lattice of even, zero-sum vectors. This lattice has integral basis $e_j+e_{-j}-2e_0$, for $1\le j\le d=(q-1)/2$. On it $J=0$. The restrictions $M,N$ commute, since convolution on a cyclic group commutes, so
$$
(M+iN)(M-iN)=2396I_d.
$$
Consequently, for integers $a,b$ with $a+ib=\det(M+iN)$, one has $a^2+b^2=2396^d$. The prime 599 is $3\bmod4$, hence has even valuation in any nonzero sum of two integer squares. To see this, if $599\mid a^2+b^2$ and either residue is nonzero, division gives a square root of $-1$ modulo 599. Thus 599 divides both $a,b$, and one can remove a factor $599^2$ and repeat. Here $2396=4\cdot599$ and $d$ is 1, 3 or 9. This contradiction forces each of the three images to have odd order.

The same determinant argument applies to any odd Legendre length $n$ and any prime divisor $q\equiv3\pmod4$ whenever $2(n+1)$ has a prime $3\bmod4$ to odd valuation. In that case both $q$-point projections cannot be even at the same time. This part of the argument uses no enumeration.

## From the quotient to the full group

The three odd-order images are contained in the squares modulo 3, 7 and 19. The resulting group modulo $399=3\cdot7\cdot19$ has order $1\cdot3\cdot9=27$. Reduction from units modulo 1197 has kernel $\{1,400,799\}$, cyclic of order three. If $H$ met that kernel nontrivially, it would contain 400. Even one word fixed by 400 gives a combined correlation at shift 399 of at least 266 by the prime-square bound ($p=3$, $m=133$), contradicting −2. Hence $H$ injects under reduction. [Prime-square theorem in Lean](../hadamard-2396-projections/PrimeCycles.lean)

If $|H|=27$, its image would be the entire product of the square groups modulo 7 and 19, acting trivially modulo 3. Both 399-point projections would then satisfy exactly the simultaneous independent square symmetries ruled out by the archived exhaustive search. Thus $|H|$ divides 9. Normalizing each word to sum 1 also covers common multipliers defined up to separate translations of the two words. The negative support has size 598, a unit modulo 1197, so translating each support to make its element sum zero converts all its multipliers into fixed multipliers simultaneously. [Finite check and normalization argument](../hadamard-2396-projections/README.md)

Enumerating the subgroups of units modulo 1197 leaves one trivial group, twelve candidates of order 3 and eighteen of order 9 after these exclusions. Three of the order-9 candidates contain 463. These counts describe remaining search cases. Existence of a length-1197 pair is open. [Reproduce the subgroup census](groups.py)
