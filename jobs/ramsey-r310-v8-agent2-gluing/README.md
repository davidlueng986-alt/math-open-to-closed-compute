# Ramsey R(3,10) — Agent 2: C++20 Bitmask Gluing & Exact Combinatorial Engine PoC

Offline C++20 (`g++ -std=c++20 -O3 -march=native`) exact combinatorial gluing prototype and controlled benchmark on the hard `D6-N9-B3` tasks (`P000-T01`, `P000-T02`, `P002-T01`). No bulk GitHub Actions workflows were launched.

## 1. Two Exact Structural Theorems (Zero-Cost Pruning Across D678)

Let `W` be a saturated triangle-free 40-vertex graph with `alpha(W) <= 9`, root `0` of degree `d`, adjacent minimum-degree neighbor `1` of degree `q`, `X = N(0) \ {1}` (`|X| = d - 1`), `Y = N(1) \ {0}` (`|Y| = q - 1`), `T = V(W) \ ({0,1} U X U Y)` (`|T| = 40 - d - q`), and `t = e(X, Y)`.

1. **Theorem 1 (`alpha(G[X,Y]) <= 9` Lower Bound)**: Since `X` and `Y` are independent, the isolated sets `Y_0 = {y in Y : N_X(y) = empty}` and `X_0 = {x in X : N_Y(x) = empty}` satisfy `|X| + |Y_0| <= 9` and `|Y| + |X_0| <= 9`, giving `|Y_0| <= 10 - d` and `|X_0| <= 10 - q`. Therefore:
   - `t >= max(0, d + q - 11)`.
   - For `D6-N9`, **`t >= 4`** (immediately proving all `T00` tasks `t in 0..2` and `t = 3` of `T01` UNSAT).
2. **Theorem 2 (`A`/`B` Singleton Upper Bound)**: Every `v in T` has `deg_X(v) >= 1` and `deg_Y(v) >= 1` by saturation. For each `x in X`, its singleton class `S_x = {v in T : N_X(v) = {x}}` is independent and nonadjacent to `A \ {x}` (size `d - 1`), so `|S_x| <= 10 - d`, hence `s_1(X) <= (d - 1)(10 - d)`. Since `e(X, T) = sx - (d - 1) - t >= 2|T| - s_1(X)`:
   - `t <= sx - (d - 1) - 2(40 - d - q) + (d - 1)(10 - d)` (and symmetrically for `Y`).
   - For `D6-N9` (`sx = 45`, `|T| = 25`), **`t <= 10`** (immediately proving all 16 tasks `T04..T07` [`t in 12..24`] and `t = 11` of `T03` UNSAT!).
   - At `t = 10`, equality holds: every `x in X` has **exact** singleton count `|S_x| = 4` (20 singletons in `T`) and the remaining 5 vertices of `T` have `deg_X(v) = 2` exactly.

Across all 12 `(d, q)` leaves of D678 (`verify_d678_t_bounds.py`), Theorems 1 & 2 eliminate **50.0%–75.0%** of the `t`-range (`D6-N6`: `1..4` [75.0% pruned]; `D6-N7`/`D7-N6`: `2..6` [73.7%]; `D6-N8`/`D8-N6`: `3..8` [72.7%]; `D6-N9`: `4..10` [72.0%]).

## 2. Exact C++20 Canonical Skeleton & Degree-Orbit Census (`D6-N9-B3`)

`d6n9_skeleton_census.cpp` enumerates all canonical bipartite graphs `G[X, Y]` under `S_X x S_Y` satisfying `deg_Y(x) <= 6`, `deg_X(y) <= 3`, and `alpha(G[X, Y]) <= 9`, then computes all `Aut(G[X,Y])`-distinct degree assignments to `Y` passing exact skeleton-level V8 convexity (`min_pairs(xt, nt) + c2_Y <= bx`, `min_pairs(yt, nt) + c2_X <= by`).

| Task | `t`-range | Effective `t` | Canonical Skeletons | Degree-Labeled Orbits | Valid Masks (avg, deg 9) | v7 Baseline |
|---|---|---|---:|---:|---:|---|
| `D6-N9-B3-P000-T01` | `3..5` | `4..5` | **5** (1 at `t=4`, 4 at `t=5`) | **79** | 1,932.6 / 7,905 (75.6% pruned) | TIMEOUT 50m (20 models, 147k cuts, OPEN:16) |
| `D6-N9-B3-P002-T01` | `3..5` | `4..5` | **5** (1 at `t=4`, 4 at `t=5`) | **10** | 1,932.6 / 7,905 (75.6% pruned) | TIMEOUT 50m (0 models, OPEN:16) |
| `D6-N9-B3-P000-T02` | `6..8` | `6..8` | **286** (16, 64, 206) | **7,699** | 1,270.7 / 7,905 (83.9% pruned) | TIMEOUT 50m (OPEN) |
| `D6-N9-B3-P001-T01` | `3..5` | `4..5` | **5** | **65** | 1,932.6 | TIMEOUT 50m (OPEN) |
| `D6-N9-B3-P003-T01` | `3..5` | `4..5` | **5** | **19** | 1,932.6 | TIMEOUT 50m (OPEN) |
| `D6-N9-B3-P002-T02` | `6..8` | `6..8` | **286** | **564** | 1,270.7 | TIMEOUT 50m (OPEN) |
| `D6-N9-B3-P003-T02` | `6..8` | `6..8` | **286** | **1,437** | 1,270.7 | TIMEOUT 50m (OPEN) |
| `D6-N9-B3-P000..3-T03` | `9..11` | `9..10` | **1,664** (510 at `t=9`, 1,154 at `t=10`) | 2,276 `t=11` skeletons killed | ~930 | TIMEOUT 50m (OPEN) |

## 3. Native C++20 Incremental CDCL(T) Engine & Controlled Benchmarks

`gluing_cdcl_v2.cpp` implements a 2-watched-literal C++20 CDCL solver with 1-UIP learning, VSIDS, Luby restarts, compact bidirectional Sinz exact-degree counters, `N_T(x_anc)` symmetry anchoring (killing `C(25,8) = 1.08M` symmetries + 28 `T-T` edges), `A`/`B` singleton caps, `I_9(X U Y)` domination, hardware-bitmask (`popcount`/`countr_zero`) incremental `I_9(H0)`/`I_9(H1)`/`I_10(W)` separation, and a standalone RUP proof verifier.

- **Self-Test (PASS)**: Proved `R(3,4) <= 9` UNSAT in **608.2 ms** (14,079 conflicts) with all **14,079 RUP steps independently verified**.
- **Controlled 15s Local PoC on Target Hard Skeletons** (Intel Xeon 8481C, 1 thread):

| Case | Free Edge Vars | Total Vars | Clauses | Models (15s) | `I_10` Cuts (15s) | Conflicts | Speed (M props/s) | Status |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `P002-T01` (`t=4 #0`, `deg6 in Y`) | 572 | 23,443 | 68,764 | 163 | 21,136 | 40,960 | 2.78 | TIMEOUT |
| `P002-T01` (`t=5 #3`, `deg6 in Y`) | 572 | 22,167 | 66,037 | 185 | 23,872 | 40,960 | 2.65 | TIMEOUT |
| `P000-T01` (`t=4 #0`, `3x deg8 in Y`) | 572 | 23,443 | 68,776 | 148 | 19,152 | 33,792 | 2.38 | TIMEOUT |
| `P000-T02` (`t=8` sample) | 572 | 21,200 | 64,018 | 155 | 19,924 | 34,816 | 2.13 | TIMEOUT |
| Python CP-SAT (`P002-T01`, `t=4 #0`, 25s) | 572 | — | — | 14 | 4,480 | — | 0.56 models/s | TIMEOUT |

### Diagnostic Codegree Ablation (`ablation_codeg.cpp`) — Explaining v7's 0-Model Timeout on `P002-T01`

| Encoding on Fixed `t=4 #0` Skeleton | Vars | Clauses | Time to Model #1 | Conflicts | Status |
|---|---:|---:|---:|---:|---|
| `XY`-codeg only (compact) | 22,531 | 65,282 | **0.048 s** | 79 | SAT_MODEL |
| `XY + XT/YT`-codeg | 73,331 | 172,649 | **0.797 s** | 1,442 | SAT_MODEL |
| `FULL` all-pairs codeg (v7-equivalent) | **145,487** | **328,305** | **>15.9 s (0 models)** | 14,336 | TIMEOUT |

**Key Diagnostic Finding**: v7's 0-model 50-minute timeout on `P002-T01` was caused by encoding all 780 pair codegrees statically (~145k+ vars, ~328k+ clauses), whereas the compact fixed-skeleton CNF is **6.5x smaller** (22.5k vars, 65k clauses) and our C++20 CDCL(T) is **19x faster** than non-incremental Python CP-SAT (10.5 vs 0.56 models/s). However, **honest negative result**: lazy `I_10` cut separation on a 40-vertex graph—even at ~1,400 cuts/s on a single fixed skeleton—still does not close a single `T01` skeleton within 15s–5m locally, because `T` (`|T|=25, e(T)=63..66`) admits huge numbers of triangle-free relaxation graphs with `alpha(T) >= 9`.

## 4. Full Solving Cost Estimate & Recommended Next Architecture

1. **Immediate Zero-Compute Wins**: Integrating Theorems 1 & 2 (`t in [d+q-11, min(t_hi_X, t_hi_Y)]`) immediately eliminates 50%–75% of all `t`-values across D678 (and mathematically closes 20/32 `D6-N9-B3` tasks + `t=3` of `T01` + `t=11` of `T03`).
2. **Skeleton-Conditioned CaDiCaL/Kissat + DRAT on `T01`**: `T01` has only **5 canonical skeletons** (`P002-T01`: 10 orbits; `P003-T01`: 19 orbits; `P001-T01`: 65 orbits; `P000-T01`: 79 orbits). Exporting our compact skeleton-conditioned CNF (with `N_T(x_anc)` fixed and `XY`-only codegrees) to CaDiCaL 1.9.5 / Kissat + `drat-trim` on GitHub Actions removes `G[X,Y]` freedom and cuts CNF size by ~5–6x, making `P002-T01` (10 orbits) and `P003-T01` (19 orbits) the highest-leverage next test (estimated ~1–5 CPU-hours for `P002-T01` if each orbit closes in 5–30 min under CaDiCaL/Kissat, vs >50 min with 0 progress in v7).
3. **Why Pure Lazy `I_10` Cutting Hits a Wall on `T02` (286 skeletons) & `T03` (1,664 skeletons)**: For `T02`/`T03`, running lazy `I_10` SAT per skeleton across 7,699–124k degree orbits would require tens of thousands of CPU-hours. Closing `D6-N9-B3` and `D678` in reasonable compute requires **replacing lazy `I_10` cutting with direct McKay/Goedgebeur `(3,9,33)` / `(3,8,25)` subgraph gluing** (enumerating valid `H0` or `T` graphs with `alpha <= 8` directly via `nauty`/`geng`-style canonical generation, then gluing `X`/`Y` attachments by bitmask intersection!).

## Files
- `d6n9_skeleton_census.cpp` — C++20 canonical `G[X,Y]` enumerator and V8-convexity degree-orbit census for `D6-N9-B3`.
- `gluing_cdcl_v2.cpp` — Native C++20 incremental CDCL(T) bitmask gluing solver with bidirectional Sinz counters, `I_9`/`I_10` bitmask separator, and RUP proof verifier.
- `ablation_codeg.cpp` — Controlled codegree ablation benchmark.
- `verify_d678_t_bounds.py` — Exact verification of Theorems 1 & 2 across all 12 D678 leaves.
- `benchmark_results.json` — Complete machine-readable benchmark and census results.
