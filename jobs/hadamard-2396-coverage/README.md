# Full cyclic correlations and exact-shift counts

The lowest complete cyclic squared error in this run is **27,328**. A different pair satisfies **310 of the 598 original shift pairs**. Both consist of two explicit sign words of length 1197 and have sum one in each word. The exact target for each combined correlation is −2. Every value in the table comes from the original words. [Sign masks](results.json) · [All 12 shards and 288 schedules](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45469531406)

| Group | Objective | Full error | Exact pairs out of 598 | Correlation at 1 | Correlation at 399 |
| --- | --- | ---: | ---: | ---: | ---: |
| Cyclic | Minimum error | 27,328 | 228 | −2 | 22 |
| Cyclic | Maximum exact count | 42,784 | 310 | −6 | 26 |
| Cyclic | Maximum count observed under 40,000 error | 39,424 | 298 | −2 | 38 |
| Elementary-3 | Minimum error | 33,312 | 165 | −2 | 14 |
| Elementary-3 | Maximum exact count | 62,624 | 309 | −2 | 26 |
| Elementary-3 | Maximum count observed under 40,000 error | 34,048 | 265 | −2 | 30 |

For a penalty $w$ the search minimizes $E/16+w\,N_{\rm fail}$, where $N_{\rm fail}$ counts original nonzero shift pairs outside target. The schedules alternate different penalties and return some endpoints to $w=0$. Each start and transition preserves the binary word sums and the square action on 19. The collector rechecks all 72 per-shard records by a scalar computation independent of the optimization. [Search schedules](coverage.py) · [All retained metrics](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/6e6c667570a02cdb5abc5af91725f0c1a1790252/runs/hadamard-2396-coverage/45469531406/results.json)

The Lean proof identifies each cyclic position with its residues modulo 63 and 19. For any two vertical columns, every square shift has the same inner product as shift 1, and every nonsquare shift has the same inner product as shift 2. The proof checks this for all pairs of three-sign columns and all 19 vertical shifts. It then proves the reduction from the ordinary one-dimensional periodic autocorrelation for every cyclic shift. For each of the three cyclic sign-mask pairs, the table of 189 values determines every original correlation. The certificate checks word normalization, exact shift count, full energy, and the original correlations at 1 and 399. [General Lean reduction](SquareAction.lean) · [Witness theorems](Coverage.lean) · [Scalar Python cross-check](check_records.py)

~~~sh
python3 jobs/hadamard-2396-coverage/check_records.py
olean=$(mktemp -d)
export LEAN_PATH="$olean"
(cd jobs/hadamard-2396-projections && lean -j1 -o "$olean/Triples.olean" Triples.lean)
(cd jobs/hadamard-2396-coverage && lean -j1 -o "$olean/SquareAction.olean" SquareAction.lean && lean -j1 Coverage.lean)
~~~

## 49 sufficient original shifts

For the 310-pair cyclic record, the square action and reflection partition all 598 original pairs into 63 classes of size nine and 31 classes of size one. The witness solves 34 size-nine classes and four singleton classes. This leaves 56 classes. If $e(s)$ denotes the original error and $e(0)=0$, then $\sum_s e(s)=0$ follows from the two word sums. It removes one more degree of freedom. Six independent equations of the form $\sum_{s\equiv t\pmod q}e(s)=0$ already hold, at the following $(q,t)$.

$$(57,1),\quad(63,30),\quad(133,3),\quad(171,5),\quad(399,10),\quad(399,27).$$

Under the same symmetry, normalization, 310 original zeros and six quotient equations, Gaussian elimination over the rationals shows that zero error on these 49 original shifts suffices for all 598 pairs.

~~~text
2 6 16 17 19 21 22 25 26 31 32 38 41 43 48 51 57
60 63 67 76 77 86 95 96 114 115 133 134 152 171 190 209
247 266 304 323 342 361 380 399 418 437 456 475 494 513 532 551
~~~

The sign-realization problem is to satisfy these simultaneously. The 309-pair elementary-3 record also leaves 49 coordinates under its own exact equations. Both coordinate lists and the independent quotient equations for all six records are printed by the checker. [Rank computation](remaining.py)


A direct seven-variable check explains the sufficiency. After the 49 listed errors vanish, the only class representatives still in question are $1,3,4,5,10,27,30$. The equations at $(63,30),(171,5),(399,10),(399,27)$ respectively give $9e_{30}=0$, $e_5=0$, $e_{10}=0$, $e_{27}=0$. The two remaining quotient equations give $e_1+e_4=0$ and $e_3+e_4+e_{10}=0$. Every one of the seven classes has size nine in the half-range. The zero-sum identity therefore gives $9(e_1+e_3+e_4+e_5+e_{10}+e_{27}+e_{30})=0$. Substitution yields $e_4=0$ and hence all seven vanish. In the displayed column order, using normalization first and then the six quotients in the order of the displayed $(q,t)$ list, the integer coefficient matrix has determinant −81. The checker constructs its entries by counting actual shifts in each residue class.
