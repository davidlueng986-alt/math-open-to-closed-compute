# Ramsey R(3,10) — Wave 2 Subagent 2: D9-C5, D9-C4, D9-C3 Exact Pruning, Compact CNF & Sharded Workflow

Exact pure-integer pruning engine, independent zero-solver Farkas verifier, unified compact CNF + single-pass Proof-First Kissat/`drat-trim`/`lrat-check` solver, and manual GitHub Actions workflow for the remaining 9-regular `D9` subcases $c \in \{5, 4, 3\}$.

## 1. Exact Pure-Integer Pruning & Local Closures

For a 9-regular triangle-free 40-vertex graph $G$ with $\alpha(G) \le 9$ and global maximum non-edge codegree $c \in \{3, 4, 5\}$, fixing non-adjacent $u, v$ with $\text{codeg}(u, v) = c$ partitions $V(G)$ into $\{u, v\}$, $S$ ($c$), $X, Y$ ($n_X = 9 - c$ each), and $T$ ($n_T = 20 + c$, $\alpha(T) \le 7$, $e(T) = 18 + 9c + e(X, Y)$).

Proved necessary pure-integer reductions (100% sound, zero floating-point exclusions):
1. **Non-edge saturation & global max codegree on $H = G[X, Y]$**: Every $x \in X$ is non-adjacent to $v$ with $N(x) \cap N(v) = N_Y(x)$, forcing $1 \le d_Y(x) \le c$ and symmetrically $1 \le d_X(y) \le c$.
2. **Pairwise codegree & Hall $b=1, 2$ on $H$**: $|N_Y(x_1) \cap N_Y(x_2)| \le c - 1$ (since $x_1, x_2$ share $u$), at most 1 singleton row per column, and at most 3 rows contained in any 2-subset of $Y$ (and symmetric).
3. **Exact skeleton-specific $(s, I_X, I_Y)$ Farkas certificates**: Every infeasible canonical skeleton orbit $H$ is certified by an exact integer vector $(y_{\text{eq}}, y_{\text{ub}})$ with $y_{\text{ub}} \ge 0$, independently verified with Python stdlib integer arithmetic in `2.05s`.

| Case | $n_T$ | Raw $e(X,Y)$ Range | Surviving $e(X,Y)$ ($e(T)$) | $e(X,Y)$ Slices Closed Locally | Valid Canonical Orbits | Farkas-Pruned Orbits | Surviving Orbits |
|---|---:|---|---|---:|---:|---:|---:|
| **D9-C5** ($c=5$) | 25 | $[2, 16]$ (15) | $[4, 14]$ ($[67, 77]$) | **4 / 15** ($\{2,3\}$ sat + $\{15,16\}$ Farkas) | 97 | **2** | **95** |
| **D9-C4** ($c=4$) | 24 | $[2, 25]$ (24) | $[5, 20]$ ($[59, 74]$) | **8 / 24** ($\{2..4, 21..25\}$ sat) | 990 | **34** | **956** |
| **D9-C3** ($c=3$) | 23 | $[4, 36]$ (33) | $[6, 18]$ ($[51, 63]$) | **20 / 33** ($\{4,5, 19..36\}$ sat) | 1,320 | **317** | **1,003** |
| **Total** | — | 72 slices | 40 slices | **32 / 72 (44.4%)** | 2,407 | **353** | **2,054** |

- Sparse certificate bundle SHA-256 (`certificates/d9c345_farkas_sparse.json`): `66f0c2c1ec80422518205425a363e79a81de0e1ebe0f74807e23fb9beb79de92`

## 2. McKay Core Files Analysis

Per Brendan McKay's [Ramsey Graphs catalog](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html) and Goedgebeur & Radziszowski (2013, [EJC 20(1) #P30](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i1p30/pdf/)):
- McKay hosts `r38_27.g6.gz` (477,142 maximal $(3,8;27)$-graphs, 4 with $e=85$), which closed `D9-C7`.
- Complete `r38_25.g6.gz`, `r38_24.g6.gz`, and `r38_23.g6.gz` files are **not hosted** and are computationally intractable for core-by-core enumeration (Goedgebeur & Radziszowski report **10,691,100** $(3,8;23, \le 52)$-graphs alone).
- Therefore, `d9c345_compact_cnf.py` uses **Mode A (Free-$T$ Skeleton-Locked Compact CNF)** as the primary solver for `C5`/`C4`/`C3`, while also supporting **Mode B (Fixed-Core $T$ Compact CNF)** with static $I_7(T)$ hitting-set clauses and zero redundant $T$-pair codegrees for any externally supplied $(3,8; n_T)$ core.

## 3. Files

- `d9c345_pruner.py` — Canonical skeleton orbit enumerator, exact integer Farkas certificate generator, and independent zero-solver verifier.
- `d9c345_compact_cnf.py` — Unified compact CNF encoder (Free-$T$ & Fixed-Core modes) + single-pass Proof-First Kissat + `drat-trim -L` + `lrat-check` + independent 40-vertex witness checker.
- `d9c345_batch_runner.py` — 10-shard round-robin batch runner ($\le 5.5$h budget/shard).
- `selftest_d9c345.py` — 6-suite local unit & soundness verification suite.
- `certificates/d9c345_pruning_summary.json` & `certificates/d9c345_farkas_sparse.json` — Verified pruning summary and all 353 exact integer Farkas certificates.
- `.github/workflows/ramsey-r310-v8-w2-d9c345.yml` — Manual `workflow_dispatch` workflow (`case` $\in \{\text{C5}, \text{C4}, \text{C3}, \text{ALL}\}$, max 10 parallel jobs, $\le 6$h/job).
