# Ramsey R(3,10) V8 Wave 2 — Unified NA-DAG Tier-1 `D6` Production Solver, Pruner & Workflow

Production-ready pure-integer pruner, compact fixed-core CNF encoder, proof-first Kissat + `drat-trim` / `lrat-check` worker, sharded batch runner, and verification suite for the **Tier-1 `D6` ($\delta(G) = 6$, $n_6(G) \ge 1$)** obligation of the Unified Non-Adjacent-Root DAG.

## 1. Mathematical Completeness (All 9 Tier-1 `D6` Branches)

Every saturated triangle-free $(3, 10; 40)$-graph $W$ with $\delta(W) = 6$ ($333$ surviving Farkas profiles out of $931$ initial / $543$ surviving) contains a degree-6 vertex $u$ and a non-adjacent vertex $v \in H_u = W - N[u]$ of internal degree $r = \deg_{H_u}(v) \in \{5, 6, 7\}$ and $W$-degree $q \in \{r+1, \dots, 9\}$ (codegree $c = q - r \in \{1, 2, 3, 4\}$) such that $T = W - N[u] - N[v]$ satisfies:
$$T \in \mathcal{R}(3, 8; 32 - r), \qquad e(3, 8, 32 - r) \le e(T) \le \min(\text{E8MAX}[32 - r],\; 132 - 8r).$$

This yields **9 exhaustive branches** covering all 333 `D6` profiles with zero omitted sub-branches:
- **$r = 5$ ($n_T = 27$, $e(T) \in [85, 92]$)**: `D6-R5-Q6` ($c=1$), `D6-R5-Q7` ($c=2$), `D6-R5-Q8` ($c=3$), `D6-R5-Q9` ($c=4$) — all cores lie inside McKay's complete 477,142-graph `r38_27.g6.gz` census.
- **$r = 6$ ($n_T = 26$, $e(T) \in [73, 84]$)**: `D6-R6-Q7` ($c=1$), `D6-R6-Q8` ($c=2$), `D6-R6-Q9` ($c=3$).
- **$r = 7$ ($n_T = 25$, $e(T) \in [65, 76]$)**: `D6-R7-Q8` ($c=1$), `D6-R7-Q9` ($c=2$).

In addition, exact pure-integer Farkas certificates prove **207 / 333** `D6` profiles force a degree-6 vertex with $e(H_u) \le 121$ (only 14,395 `(3,9; 33)` graphs total per Angeltveit 2024), leaving 126 residual `D6` profiles.

## 2. Exact Pure-Integer Pruning Results (`d6_nadag_pruner.py`)

Combining Agent 4's Tier-1 `D6` decomposition with Agent 1's 4 exact pure-integer inequalities (saturation/König cross-edge bounds + $\deg_T \le 7$, rooted singleton caps on $A, B, X, Y$, shared-root/non-edge codegree caps, and exact water-filling degree-capped & singleton-capped convexity):

| Branch | $(r, q, c)$ | $n_T$ | $e(T)$ Window | $t = e(X,Y)$ | Agent 4 Profiles | **Combined Profiles** | Newly Pruned (Agent 1) | Agent 4 Triples | **Combined Triples** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `D6-R5-Q6` | (5,6,1) | 27 | [85, 92] | [5, 16] | 242 | **242** | 0 | 2,890 | **1,999** |
| `D6-R5-Q7` | (5,7,2) | 27 | [85, 92] | [5, 16] | 269 | **269** | 0 | 3,062 | **2,309** |
| `D6-R5-Q8` | (5,8,3) | 27 | [85, 92] | [5, 15] | 304 | **242** | **62** | 3,003 | **2,025** |
| `D6-R5-Q9` | (5,9,4) | 27 | [85, 92] | [5, 10] | 333 | **213** | **120** | 1,994 | **1,273** |
| `D6-R6-Q7` | (6,7,1) | 26 | [73, 84] | [6, 18] | 269 | **269** | 0 | 3,291 | **2,575** |
| `D6-R6-Q8` | (6,8,2) | 26 | [73, 84] | [6, 18] | 304 | **304** | 0 | 3,474 | **2,928** |
| `D6-R6-Q9` | (6,9,3) | 26 | [73, 84] | [6, 17] | 333 | **269** | **64** | 3,496 | **2,529** |
| `D6-R7-Q8` | (7,8,1) | 25 | [65, 76] | [7, 20] | 304 | **304** | 0 | 3,721 | **3,208** |
| `D6-R7-Q9` | (7,9,2) | 25 | [65, 76] | [7, 20] | 333 | **333** | 0 | 3,821 | **3,533** |
| **Total** | **9 branches** | 25–27 | 8–12 edges | — | **2,691** | **2,445** | **+246** | **28,752** | **22,379 (-22.17%)** |

All **552** pruned `(branch, profile)` pairs (306 Agent 4 + 246 Agent 1), **388** base Farkas profile exclusions, and **207** forced $e(H_u) \le 121$ Farkas certificates are independently verified in pure-integer stdlib-only Python (`python3 d6_nadag_pruner.py --verify-only out_pruner`).

## 3. Files

- `d6_nadag_pruner.py`: Exact pure-integer Farkas + Agent 1/Agent 4 pruner, certificate generator, and stdlib-only verifier.
- `d6_core_cnf.py`: Compact fixed-core DIMACS CNF encoder (307–360 primary vars, static $I_7(T)$ hitting-set clauses on $A, B, X, Y$, Hall $b=1$, $S$-domination, strict `lex_lt`), proof-first Kissat + `drat-trim -L` + `lrat-check` worker, and independent SAT witness verifier.
- `d6_batch_runner.py`: Deterministic sharded runner ($\le 10$ shards, $\le 5.5\text{h}$ cap) with atomic checkpointing and `poc` / `full` modes.
- `selftest_d6_nadag.py`: Complete 5-part local verification suite.
- `d6_nadag_summary.json`: Verified local pruner summary and certificate SHA-256 digest.
- `.github/workflows/ramsey-r310-v8-w2-nadag-d6.yml`: Manual `workflow_dispatch`-only workflow pinned to `ghcr.io/davidlueng986-alt/math-compute-sat@sha256:fa5d94d4e8dc2aaccec31230adea72967257f9bbe732db9f4c7df6046f2a6dbc`.

## 4. Local Verification

```bash
OPENBLAS_NUM_THREADS=1 python3 jobs/ramsey-r310-v8-w2-nadag-d6/d6_nadag_pruner.py --out-dir out_pruner
python3 jobs/ramsey-r310-v8-w2-nadag-d6/d6_nadag_pruner.py --verify-only out_pruner
python3 jobs/ramsey-r310-v8-w2-nadag-d6/selftest_d6_nadag.py
```
