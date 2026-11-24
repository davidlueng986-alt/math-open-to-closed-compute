# Order 2396 via a length-1197 Legendre pair

Two explicit length-1197 sign words, each with sum 1, attain the required combined periodic autocorrelation **−2 on every nonzero shift in the subgroups of orders 63 and 19**. These subgroups intersect only at zero, giving 80 nonzero shifts, or 40 pairs up to reflection. Across all 598 pairs the witness satisfies 88. Its shift-one value is −22, so the order-2396 construction remains open. [Two hexadecimal sign masks](certificate.json) · [Exact checker](check.py) · [Lean certificate](Diagonal.lean)

The same words satisfy all 57-, 63- and 133-point compression equations. The union of the sampled Fourier frequencies contains 224 nonzero indices, each with combined squared magnitude 2396. The previous witness realized these same equations with different numerical margins and satisfied 22 prescribed original shift pairs. The new witness strictly extends that set of prescribed shifts. Its full squared error is 709,920. The previous search's best full-error candidate attained 196,288 under a separate objective. [Numerical margins and starting lift](seed.json) · [Previous certificates](../hadamard-2396-projections/README.md)

Any common multiplier group of a genuine length-1197 pair must have order dividing 9. A determinant argument rules out even images at 3, 7 and 19. Combined with two earlier exclusions, this leaves eighteen candidate groups of order 9. [Proof and exact scope](multipliers.md)

## Construction

Write a position as $(x,y)=(i\bmod63,i\bmod19)$. Each word is fixed by the order-three multiplier $463$, which acts as $(x,y)\mapsto(22x,7y)$. Six representatives $1,2,4,5,8,10$ generate the 18 nonzero columns in orbits of size three. Column zero is fixed as a set. At any shift $(3j,0)$ the Hamming distances in the three columns of each nonzero orbit coincide. A combined correlation of −2 requires total Hamming distance 1198, so the two singleton columns must contribute $1\bmod3$. We selected exact quotient margins admitting singleton columns with that property. CP-SAT shared one Boolean variable per multiplier orbit, imposed the three sets of margins, and required 199 constant triples at shift 399. [Optional CP-SAT reconstruction](lift.py)

For a word $W$ let $T_y(r)=\sum_{k=0}^2W(r+21k,y)$ for $0\le r<21$. For $x$-shifts the combined autocorrelation of these triples, summed over words and columns, is the sum of three original correlations at $t,t+21,t+42$. Its targets are 2390 at zero and −6 elsewhere. Multiplication by 22 permutes these three lifts transitively when $3\nmid t$. Reaching −6 then forces each corresponding original correlation to equal −2. At $t=0$, reflection and the known zero-shift correlation 2394 force the two nonzero lifts to equal −2.

The first search balances rectangles in $(x\bmod3,x\bmod7)$ across two representative columns. Each of these moves preserves all three numerical margins. Independent changes in the two words are matched on the full integer defect vector. A second search permutes the signs within individual triples while holding their sums fixed. It checks the remaining horizontal shifts and the three vertical representatives $1,2,4$ under multiplication by 7 and reflection. For the certificate the two words have 104 and 95 constant triples. Both search scores and the squared error on the 40 required shift pairs are zero. [Search code](search.cpp)

## Reproduce

Run from this directory, using Python 3.10 or newer and a C++17 compiler. A mask bit of 1 represents a negative sign, with position zero in the low bit. The checker computes all 598 correlations by both direct summation and bit rotations, and checks the margins, their correlations, the multiplier and the subgroup equations.

```sh
python3 check.py
g++ -std=c++17 -O3 -mpopcnt -Wall -Wextra -Werror search.cpp -o /tmp/hadamard-diagonal
python3 check.py --signs seed | /tmp/hadamard-diagonal both 1210 200000 300000 > /tmp/hadamard-replay.json
python3 check.py --replay /tmp/hadamard-replay.json
```

Lean 4.36.0 checks normalization, multiplier invariance at all 1197 coordinates, every projected margin and correlation, the 80 original subgroup shifts, and the failure at shift one. It imports the preceding job's definitions of signs and periodic autocorrelation. [Verification workflow](../../.github/workflows/hadamard-2396-verify.yml)

```sh
proof_dir=$(mktemp -d)
export LEAN_PATH="$proof_dir"
(cd ../hadamard-2396-projections && lean -j1 -o "$proof_dir/Triples.olean" Triples.lean && lean -j1 -o "$proof_dir/Witness.olean" Witness.lean)
lean -j1 -DwarningAsError=true Diagonal.lean
```

To seek a fresh initial lift, install `ortools==9.15.6755` and run `python3 lift.py`. Parallel CP-SAT can return different feasible words. The archived seed makes the subsequent C++ replay deterministic on the tested Linux toolchain.

The `extend57` search targets all original shifts in the subgroups of orders 63 and 57, or 58 distinct shift pairs. It adds three mixed-column equations on the triple sums and six representatives at shifts $(21,y)$. The shard checker independently reconstructs both scores from the one-dimensional original correlations and compares the reported target to the 58 shifts themselves. [Run a shard](run.sh) · [Check and merge results](merge.py)
