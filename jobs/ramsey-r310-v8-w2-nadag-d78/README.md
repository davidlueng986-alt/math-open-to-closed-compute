# Ramsey R(3,10) — Wave 2 Unified NA-DAG Tier-2 `D7` & `D8` Production Solver

Production-ready pure-integer pruner, compact fixed-`(3,8; n_T)`-core CNF encoder, proof-first Kissat + `drat-trim` + `lrat-check` sharded runner, independent SAT witness verifier, and manual GitHub Actions workflow for **Tier-2 `D78`** ($\delta(G) \in \{7, 8\}$, i.e., $n_6 = 0, n_7 + n_8 > 0$, covering 100% of all 209 surviving `D78` degree profiles from the 931 $\to$ 543 v6 Farkas partition).

## Mathematical Coverage & Exact Pure-Integer Pruning Results

Building directly on Wave 1 Agent 4 (`jobs/ramsey-r310-v8-agent4-dag/`, commit `1f4691d2`) and Wave 1 Agent 1 (`jobs/ramsey-r310-v8-agent1-pruning/`, commit `89faecc9`):

- **100% Tier-2 `D78` Coverage**: Every saturated $(3,10;40)$-graph with $n_6=0, n_7+n_8>0$ has $T^*(W) = \max_{x \not\sim y} |T(x,y)| \in \{24, 25, 26, 27\}$ ($T^* \le 23$ Farkas-refuted for all 209 `D78` profiles) and attains a lex-max root degree pair $(d_u, d_v)$ in $(9,9) > (8,9) > (8,8) > (7,9) > (7,8) > (7,7)$, yielding **23 algebraic branches**.
- **Pure-Integer Pruning (Zero Floating-Point Trust)**:
  - **209 / 209** `D78` profiles certified impossible at $T^* \le 23$ by exact integer Farkas vectors.
  - **972 / 4,313** candidate `(branch, profile)` pairs pruned by tie-broken exact integer Farkas (`lp_kept = 3,341`), completely closing **`D78-T24-D78-C1`** (`171/171` refuted).
  - **75** additional `(branch, profile)` pairs closed by NA-DAG + Agent 1 pure-integer inequalities (`3,341 -> 3,266`).
  - **84** additional `(branch, profile, t)` triples removed beyond Agent 4's baseline (`29,433 -> 29,349`, across `D78-T27-D99-C7`, `D78-T27-D79-C5`, `D78-T27-D77-C3`, `D78-T25-D79-C3`).
  - **22 surviving nonempty Tier-2 `D78` branches**, independently verified to cover all **209 / 209** `D78` profiles with zero gaps.

## Fixed-Core Compact CNF Size Benchmarks (Real `(3,8; 27, 85)` Core, 750 $I_7$ Baked In)

| Branch | $t = e(X,Y)$ Range | Primary Vars | Total Vars | Clauses | Static $I_7$ |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `D78-T27-D99-C7` | `[2, 4]` | 301 | 71,466 | 146,258 | 750 |
| `D78-T27-D89-C6` | `[3, 6]` | 303 | 46,551 | 95,408 | 750 |
| `D78-T27-D88-C5` | `[3, 9]` | 306 | 45,423 | 92,564 | 750 |
| `D78-T27-D79-C5` | `[4, 8]` | 305 | 45,299 | 92,182 | 750 |
| `D78-T27-D78-C4` | `[4, 12]` | 309 | 44,510 | 89,934 | 750 |
| `D78-T27-D77-C3` | `[4, 16]` | 313 | 44,047 | 88,433 | 750 |

## Compute Estimates (Based on V8 PoC Run 3: 4.7–17.4 min/core on 1-pass Kissat + `drat-trim`)

- **PoC Mode (`mode=poc`, 6 `T*=27` branches $\times$ 4 McKay `(3,8;27,85)` cores = 24 units)**:
  - At ~10 min/core average, ~4 CPU-hours total; **~1.0 hour wall-clock** on 4 parallel shards (well within the 5.5h per-shard cap).
- **Full `T*=27` $e(T) \in [85, 94]$ Sweep**:
  - McKay's complete `r38_27.g6.gz` census contains 477,142 graphs; lower-edge strata (`e=85`: 4 cores; `e=86`: small census) can be swept in waves of `<= 10` parallel shards (`<= 5.5h`/shard), while core-level pure-integer prefiltering (`codeg_T(a,b) > max_cap`) instantly eliminates non-qualifying cores before invoking Kissat.

## Files & Local Reproduction

- `d78_nadag_pruner.py` — Exact pure-integer Farkas + Agent 1 4-inequality pruner & zero-solver stdlib verifier.
- `d78_core_cnf.py` — Compact fixed-`(3,8; n_T)`-core CNF encoder (core prefilter, $I_7$ hitting sets, Hall $b=1/2$, $S$-domination, lex symmetry breaking) + Kissat/`drat-trim`/`lrat-check` proof-first worker + independent SAT witness verifier.
- `d78_batch_runner.py` — Sharded runner (`<= 10` shards, `<= 5.5h` budget, `poc`/`full` modes) + streaming McKay `r38_27.g6.gz` extractor.
- `selftest_d78_nadag.py` — Full 6-part local verification suite.
- `.github/workflows/ramsey-r310-v8-w2-nadag-d78.yml` — Manual `workflow_dispatch`-only workflow (`math-compute-sat` pinned digest, `<= 10` parallel shards, `<= 6h`/job).

```bash
OPENBLAS_NUM_THREADS=1 python3 d78_nadag_pruner.py --out-dir out_pruner
OPENBLAS_NUM_THREADS=1 python3 selftest_d78_nadag.py --pruner-dir out_pruner
```
