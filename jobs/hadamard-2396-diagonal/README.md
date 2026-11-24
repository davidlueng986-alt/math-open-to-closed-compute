# Order 2396 via a length-1197 Legendre pair

Two explicit length-1197 sign words simultaneously attain the required combined periodic autocorrelation **−2 at all 116 nonzero shifts in the subgroups of orders 57 and 63**. Each word sums to 1. The two subgroups meet in the order-3 subgroup, giving 58 independent shift pairs up to reflection. The words pass 85 of all 598 pairs. At shift 1 the sum is 46, so construction of a Hadamard matrix of order 2396 remains open. [Extension sign masks](extension.json) · [Exact checker](check.py) · [Lean proof of all 116 shifts](Extension.lean)

Both words also satisfy all 57-, 63- and 133-point compression equations. The union of the sampled Fourier frequencies contains 224 nonzero indices, each with combined squared magnitude 2396. The intermediate witness had the same numerical margins and solved the 63- and 19-order subgroups. An earlier construction with different margins solved 22 prescribed original shift pairs. [Margins and starting lift](seed.json) · [Intermediate signs](certificate.json) · [Earlier witnesses](../hadamard-2396-projections/README.md)

| Witness | Guaranteed original shift pairs | All exact pairs out of 598 | Correlation at shift 1 | Full squared error |
| --- | ---: | ---: | ---: | ---: |
| Orders 63 and 19 | 40 | 88 | −22 | 709,920 |
| Orders 63 and 57 | 58 | 85 | 46 | 1,159,296 |

Both target errors are zero. The earlier search minimizing full squared error attained 196,288 with a different witness. [Full-error record](../hadamard-2396-projections/original-search.json)

Any common multiplier group of a genuine length-1197 pair must have order dividing 9. A determinant argument rules out even images at 3, 7 and 19. Combined with two earlier exclusions, this leaves eighteen candidate groups of order 9. [Proof and exact scope](multipliers.md)

## Construction

Write a position as $(x,y)=(i\bmod63,i\bmod19)$. Each word is fixed by the order-three multiplier $463$, which acts as $(x,y)\mapsto(22x,7y)$. Six representatives $1,2,4,5,8,10$ generate the 18 nonzero columns in orbits of size three. Column zero is fixed as a set. At any shift $(3j,0)$ the Hamming distances in the three columns of each nonzero orbit coincide. A combined correlation of −2 requires total Hamming distance 1198, so the two singleton columns must contribute $1\bmod3$. We selected exact quotient margins admitting singleton columns with that property. CP-SAT shared one Boolean variable per multiplier orbit, imposed the three sets of margins, and required 199 constant triples at shift 399. [Optional CP-SAT reconstruction](lift.py)

For a word $W$ let $T_y(r)=\sum_{k=0}^2W(r+21k,y)$ for $0\le r<21$. For $x$-shifts the combined autocorrelation of these triples, summed over words and columns, is the sum of three original correlations at $t,t+21,t+42$. Its targets are 2390 at zero and −6 elsewhere. Multiplication by 22 permutes these three lifts transitively when $3\nmid t$. Reaching −6 then forces each corresponding original correlation to equal −2. At $t=0$, reflection and the known zero-shift correlation 2394 force the two nonzero lifts to equal −2.

The first search balances rectangles in $(x\bmod3,x\bmod7)$ across two representative columns. Each of these moves preserves all three numerical margins. Independent changes in the two words are matched on the full integer defect vector. A second search permutes the signs within individual triples while holding their sums fixed. It checks the remaining horizontal shifts and the three vertical representatives $1,2,4$ under multiplication by 7 and reflection. For the intermediate 63/19 certificate the two words have 104 and 95 constant triples. Both search scores and the squared error on the 40 required shift pairs are zero. [Search code](search.cpp)

The order-57 extension adds three quotient equations for column shifts $y=1,2,4$ and six original representatives $(21,y)$ for $y=1,2,4,5,8,10$. A 12-shard run made 72 trials. Seed 1250 in shard 6 reached zero quotient error and solved 56 of the 58 target pairs. Its two remaining original correlations were 10 at shift 342 and −14 at shift 456. Restarting only the within-triple phase search with seed 710 solved both. The resulting words have 98 and 101 constant triples. [Public run](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45324284634) · [Per-seed results](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/b6f6da9d0efc8295e69e40455692827e88708561/runs/hadamard-2396-diagonal/45324284634/summary.json) · [Three-stage replay](replay.py)

## Reproduce

Run from this directory, using Python 3.10 or newer and a C++17 compiler. A mask bit of 1 represents a negative sign, with position zero in the low bit. The checker computes all 598 correlations by both direct summation and bit rotations, and checks the margins, their correlations, the multiplier and the subgroup equations.

```sh
python3 check.py
g++ -std=c++17 -O3 -mpopcnt -Wall -Wextra -Werror search.cpp -o /tmp/hadamard-diagonal
python3 replay.py /tmp/hadamard-diagonal
```

Lean 4.36.0 checks normalization, multiplier invariance at all 1197 coordinates, every projected margin and correlation, the 80 original subgroup shifts of the first witness, the 116 of the second, and both failures at shift one. It imports the preceding job's definitions of signs and periodic autocorrelation. [Verification workflow](../../.github/workflows/hadamard-2396-verify.yml)

```sh
proof_dir=$(mktemp -d)
export LEAN_PATH="$proof_dir"
(cd ../hadamard-2396-projections && lean -j1 -o "$proof_dir/Triples.olean" Triples.lean && lean -j1 -o "$proof_dir/Witness.olean" Witness.lean)
lean -j1 -DwarningAsError=true -o "$proof_dir/Diagonal.olean" Diagonal.lean
lean -j1 -DwarningAsError=true Extension.lean
```

To seek a fresh initial lift, install `ortools==9.15.6755` and run `python3 lift.py`. Parallel CP-SAT can return different feasible words. The archived seed makes the subsequent C++ replay deterministic on the tested Linux toolchain.

The shard checker independently reconstructs both scores from the one-dimensional original correlations and compares the reported target to the 58 shifts themselves. [Run a shard](run.sh) · [Check and merge results](merge.py)
