# Hadamard order 2396

A Legendre pair of length 1197 would give a Hadamard matrix of order 2396. The strongest subgroup certificate here is a pair of actual sign words whose autocorrelations satisfy every required equation on the subgroups of orders 7, 9, 19 and 21. It also realizes three exact Fourier projections. Its first original correlation is 10, with required value −2. The order-2396 construction remains open. [Sign certificates](original-search.json) · [12-shard search](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45301240776)

## What the certificates satisfy

Write $P_A(s)=\sum_{i=0}^{1196}A_iA_{i+s}$, with cyclic indices, and similarly for $B$. Each word sums to 1. A solution requires $P_A(s)+P_B(s)=-2$ at all 598 shifts up to reflection. The last column below uses $E=\sum_{s=1}^{598}(P_A(s)+P_B(s)+2)^2$.

| Pair | Complete original subgroups checked | Exact original shift pairs, out of 598 | $P_A(1)+P_B(1)$ | $E$ |
| --- | --- | ---: | ---: | ---: |
| Initial CP-SAT lift | order 3 | 23 | 30 | 1,157,952 |
| Mixed-subgroup witness | orders 7, 9, 19, 21 | 49 | 10 | 1,051,296 |
| Lowest full energy in this search | order 3 | 51 | −30 | 196,288 |

The four subgroups impose 22 distinct original shift pairs, or 44 nonzero shifts including reflections. The mixed witness passes a further 27 pairs. Its 97 constant three-cycles on the first row and 102 on the second give the required total 199. The bit at position $i$ in each hexadecimal mask is 1 exactly when the corresponding sign is −1. [Original masks](original-search.json) · [Exact integer checker](verify.py)

For each $q$ below, put $m=1197/q$ and $U_j=\sum_{i\equiv j\pmod q}A_i$, with $V$ defined from $B$. A Legendre pair needs $P_U(0)+P_V(0)=2396-2m$ and $P_U(s)+P_V(s)=-2m$ at every nonzero quotient shift. These identities follow by summing the original correlations in each residue class. All named candidates realize the same arrays and satisfy all three systems.

| $q$ | $m$ | At zero | At every nonzero shift |
| ---: | ---: | ---: | ---: |
| 57 | 21 | 2354 | −42 |
| 63 | 19 | 2358 | −38 |
| 133 | 9 | 2378 | −18 |

The Fourier transform on each quotient samples the full transform at multiples of $1197/q$. Their union contains **224 distinct nontrivial frequencies**, each with combined squared modulus 2396. These frequencies overlap across quotients. They measure a different condition from the 22 original shift pairs. The finite proof checks every margin against the mixed witness bits and every quotient correlation against the table. [Quotient arrays](witness.json) · [Lean margin and correlation proofs](Witness.lean) · [Lean original-shift and failure proofs](RawShifts.lean)

## A multiplier obstruction for every odd prime square

Let $n=p^2m$, where $p$ is an odd prime and $m\ge1$, and let $d=pm$. If either word is fixed by the coordinate multiplier $u=1+d\pmod n$, then
$$
P_A(d)+P_B(d)\ \ge\ 2m.
$$
The single equation at $d$ therefore rules out this multiplier on either word of a Legendre pair. The Lean theorem uses the ordinary divisor definition of primality and derives the inverse property modulo $p$ by Bézout. [Formal theorem and proof](PrimeCycles.lean)

To see the bound, split the coordinates into $d$ cycles $i+jd$, each of odd length $p$. Every binary cycle has an adjacent agreement, so contributes at least $2-p$ to the correlation at $d$. On a cycle, multiplication by $u$ sends $j$ to $j+i$ modulo $p$. When $p\nmid i$ this is a full cycle. Thus $(p-1)m$ cycles in the fixed word are constant and each contributes $p$. The other $m$ cycles in that word, and all $pm$ cycles in the second word, contribute at least $2-p$ each. Adding gives the displayed bound.

For $n=1197$ this excludes multiplier 400 even if just one word is fixed. More specifically, for $n=3d$ and $c_A$ the number of constant triples, each triple contributes 3 or −1, so $P_A(d)=4c_A-d$. At $d=399$ the pair must have $c_A+c_B=199$. Invariance by 400 already forces at least 266 constant triples in a single word. Related work of Ramos, Hulak and de Queiroz studies multiplier obstructions at length 333. [Triple identity in Lean](Triples.lean) · [Related work](https://arxiv.org/abs/2607.20765v2)

The coordinate conclusion also excludes this multiplier up to cyclic translation on normalized odd-length words. If $D$ is the set of negative entries, $k=|D|=(n-1)/2$ is a unit modulo $n$. From $uD=D+c$, summing elements gives $(u-1)\sum D=kc\pmod n$. Translating $D$ by $-k^{-1}\sum D$ makes it fixed by $u$ and preserves its cyclic correlations. This normalization argument is recorded here in ordinary mathematics.

## A finite exclusion at 399

Consider the 399-point projections of a hypothetical pair. Suppose both projected words are invariant under the independent quadratic residues modulo 7 and modulo 19, acting trivially modulo 3. Every such pair fails a required 399-point equation. This scope permits an arbitrary action-free coordinate modulo 3. The words in the positive certificates use weaker symmetry.

The entries of a 399-point word are in $\{-3,-1,1,3\}$. Its pair must have combined squared norm 2390, forcing 199 entries of magnitude 3 among 798 entries. Compression to 133 leaves nine orbit cells per word. Normalize the signs so both row sums are 1 and orient the first row at each prime by a simultaneous nonsquare multiplier if needed. Two enumerations give the same eight ordered, normalized shape pairs. One uses prime Gauss sums. The other multiplies cells with their exact orbit multiplicities.

For each shape, the C++ search enumerates all ordered triples in $\{-3,-1,1,3\}^3$ above each cell. It checks whether the magnitude-three counts can add to 199, and uses the 3-point projected norm bound 1598 for each row. A linear combination of all 200 cyclic correlation coordinates modulo $2^{64}$ gives a necessary additive matching condition. Every collision is kept and compared with the original integer equations. Across the eight cases there were zero hash matches. Each run also recovered a prescribed positive-control match and checked its hash against scalar correlations. [Shape enumeration](shapes.py) · [Independent enumeration](check_shapes.py) · [399-point enumeration](search399.cpp) · [Archived results](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/d9a5be164a58c45cb608e0272f1493c126ec82b1/runs/hadamard-2396-projections/45298481173/results.json)

## Search and replay

The previous 63-point squared residual was 8288 with fixed 9- and 7-point margins. Changing those margins and matching the norm and determinant of two triples over the Eisenstein integers gave an exact 63-point layer. For the winning 7- and 9-point margins, the specified orbit search returns 716 ordered solutions. The 57- and 133-point layers use quadratic residues modulo 19. The listed orbit parameters regenerate all three layers, then CP-SAT can seek full sign words with those same margins and exactly 199 constant triples. [Construction](construct.py) · [CP-SAT model](lift.py)

The subsequent search changes four signs on a balanced rectangle in the $9\times7\times19$ array, or eight on two rectangles with opposing 57-point changes. Every allowed change preserves all three margins. Simulated annealing optimizes original correlations and locks shift 399. A meet-in-the-middle repair also tries up to two disjoint changes on each word, including their exact cross terms. Two of twelve shards attained all four target subgroups. The best full-energy witness used a separate 598-shift objective. [Trade search](trades.cpp) · [Shard program](../hadamard-2396-trades/search.py) · [Mixed-subgroup run data](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/18199fd35471dff34a208a73418ee0a297baa9a9/runs/hadamard-2396-trades/45301240776/results.json)

From the full-energy endpoint $E=196288$, all 5,474 admissible single trades worsen the score. Allowing one trade on each word also permits their changes at shift 399 to cancel. The resulting 12,314,963 distinct nonidentity neighbors all have $E \ge 196416$. This covers the stated four- or eight-sign trade on each word. After 3, 5, 8 or 11 random valid trades, eight independent restarts followed by paired descent returned energy 196288 seven times and 202880 once. [Independent neighborhood census](check_neighborhood.py) · [Endpoint](original-search.json)

Run from this directory. Standard Python 3.10 or later suffices for the scalar and packed checkers and the projected construction. The optional lift uses OR-Tools 9.15.6755. The independent neighborhood census uses NumPy.

```sh
python3 verify.py
python3 construct.py
python3 check_shapes.py
# Optional binary-lift search after installing the pinned dependency
python3 -m pip install ortools==9.15.6755
python3 construct.py --lift 30
# Reproduce the lowest full-energy candidate
g++ -std=c++17 -O3 -Wall -Wextra -Werror trades.cpp -o /tmp/hadamard-trades
python3 verify.py --signs seed | /tmp/hadamard-trades 420 all 330000
python3 verify.py --signs energy | /tmp/hadamard-trades 1 paired 1
python3 check_neighborhood.py
# Replay one uphill escape attempt
python3 verify.py --signs energy | /tmp/hadamard-trades 9903 perturb 11 | /tmp/hadamard-trades 1 paired 30
```

The manual GitHub verification workflow replays the Python certificates and all four Lean files. Lean 4.36.0 with its standard library suffices. [Verification workflow](../../.github/workflows/hadamard-2396-verify.yml) The finite certificates use kernel reduction. The reported theorem dependencies are Lean's standard axioms.

```sh
proof_dir=$(mktemp -d)
export LEAN_PATH="$proof_dir"
lean -j1 -DwarningAsError=true -o "$proof_dir/Triples.olean" Triples.lean
lean -j1 -DwarningAsError=true PrimeCycles.lean
lean -j1 -DwarningAsError=true -o "$proof_dir/Witness.olean" Witness.lean
lean -j1 -DwarningAsError=true RawShifts.lean
```
