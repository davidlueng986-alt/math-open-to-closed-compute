# Ramsey R(3,10) V8 — Agent 3: SAT Encoding, CP-SAT & SMS Redesign

**Scope**: First-principles audit of v5/v7 CNF bloat, local OR-Tools CP-SAT proof-of-concept benchmarks on the exact hard tasks (`D6-N9-B3-P000-T01`, `D6-N9-B3-P002-T01`, `D8-N8-B0-P000-T01`), and a Lean-CNF + SMS (`smsg`/`pysms`) + Proof-First Kissat/CaDiCaL redesign for `ghcr.io/davidlueng986-alt/math-compute-sat`. No bulk GitHub Actions launched.

## 1. Exact v5/v7 CNF Bloat Audit

Reconstructing the exact v5/v6/v7 task definitions (`reconstruct_tasks.py`: 543 surviving v6 profiles, 279 total tasks = 32 pilot + 247 rollout) and instrumenting every constraint block of `v5/solve.py` + `v7/worker.py` (`audit_v5_v7_bloat.py`) reveals that v5/v7's base CNF is **380k–426k variables and 1.02M–1.18M clauses** for graphs with only **661–665 free edge variables** (**572x–644x variable blowup**).

| Constraint Block | `D6-N9-B3-P000-T01` Vars (%) | `D6-N9-B3-P000-T01` Clauses (%) | `D6-N9-B3-P002-T01` Vars (%) | `D8-N8-B0-P000-T01` Vars (%) | `D8-N8-B0-P000-T01` Clauses (%) |
|---|---:|---:|---:|---:|---:|
| `1_skeleton_fixed` | 0 (0.0%) | 115 (0.0%) | 0 (0.0%) | 0 (0.0%) | 119 (0.0%) |
| `2_triangles` | 0 (0.0%) | 7,200 (0.7%) | 0 (0.0%) | 0 (0.0%) | 7,064 (0.6%) |
| `3_vertex_degrees` | 5,335 (1.4%) | 31,653 (3.1%) | 5,335 (1.4%) | 5,290 (1.2%) | 31,372 (2.7%) |
| `4_profile_histogram` | 537 (0.1%) | 2,957 (0.3%) | 503 (0.1%) | 760 (0.2%) | 5,122 (0.4%) |
| `5_edge_counts_m_H0_H1_T_t` | 7,652 (2.0%) | 45,712 (4.5%) | 7,652 (2.0%) | 7,428 (1.7%) | 44,370 (3.8%) |
| **`6_dual_internal_degrees`** | **60,721 (16.0%)** | **122,887 (12.0%)** | **60,721 (16.0%)** | **58,058 (13.6%)** | **117,458 (9.9%)** |
| **`7_codegrees_and_saturation`** | **109,127 (28.7%)** | **324,260 (31.7%)** | **109,127 (28.7%)** | **107,834 (25.3%)** | **320,207 (27.1%)** |
| `8_deficit_eps_sums` | 0 (0.0%) | 0 (0.0%) | 0 (0.0%) | 21,190 (5.0%) | 123,476 (10.5%) |
| **`9_HB_neighborhood_patterns`** | **194,819 (51.2%)** | **468,645 (45.8%)** | **194,819 (51.2%)** | **223,290 (52.4%)** | **522,640 (44.3%)** |
| `10_lex_symmetry` | 1,330 (0.3%) | 7,449 (0.7%) | 1,330 (0.3%) | 1,330 (0.3%) | 7,425 (0.6%) |
| `11_static_seeded_I10` | 0 (0.0%) | 12,961 (1.3%) | 0 (0.0%) | 0 (0.0%) | 1,553 (0.1%) |
| **Total (Base + Seeds)** | **380,302** | **1,023,840** | **380,268** | **425,961** | **1,180,807** |

### Root Causes of the 572x–644x Blowup
1. **`9_HB_neighborhood_patterns` (51.2%–52.4% of all vars)**: `z.am(..., seqcounter)` for every subset B of A and B1 of size b in {1..4} plus sub-bounds creates 195k–223k Sinz sequential-counter variables and 469k–523k clauses.
2. **`7_codegrees_and_saturation` (25.3%–28.7% of all vars)**: 38 AND vars + 8-bound balanced totalizer for all ~765 non-fixed-true pairs = 108k–109k vars and 320k–324k clauses.
3. **`6_dual_internal_degrees` (13.6%–16.0% of all vars — 100% ALGEBRAICALLY REDUNDANT)**: `z.al(ls, 11-k)` calls `atmost(negated, 32-(11-k))` with `seqcounter` (~864 vars per vertex = 60,721 vars!). Yet for v in T, `deg_H0(v) = deg(v) - deg_X(v)`, so `deg_H0(v) <= 8` is automatic from `deg(v) <= 9, deg_X(v) >= 1`, and `deg_H0(v) >= 11-d` is identical to the root-0 codegree cap `deg_X(v) <= deg(v) + d - 11`. Analogous for Y and H1.
4. **`5_edge_counts_m_H0_H1_T_t` (7,504 vars, 45,712 clauses — 100% ALGEBRAICALLY REDUNDANT)**: Binary full-adder trees duplicate exact linear functions of the degree profile and the <=15 vertices in X union Y: `2m = sum deg(v)`, `e(H0) = m - q - sum_{x in X} deg(x)`, `e(H1) = m - d - sum_{y in Y} deg(y)`, and `e(T) = m - 1 - sx - sy + t`.
5. **Static & Reused I10 Cuts**: On `D6-N9-B3`, v7's seeded I10 length histogram is `{8: 25, 16: 10, 21: 80, 24: 140, 25: 56, 26: 12650}` (97.6% are 26-literal clauses), plus 100k+ reused 45-literal clauses from v5/v6 that cannot propagate until 44 edges are FALSE.

## 2. Exact Mathematical Strengthening: König Bound + Bipartite X x Y Skeletons

**Theorem (König Bipartite Bound)**: Since X (size d-1) and Y (size q-1) are disjoint independent sets, G[X union Y] is bipartite on d+q-2 vertices. By König's theorem, `alpha(G[X union Y]) = (d+q-2) - tau(G[X union Y]) <= 9`, hence:
`t = e(X, Y) >= tau(G[X union Y]) >= d + q - 11`.

- **Across all 279 v7 tasks**:
  - v6 baseline: **99,862** feasible `(task, profile, t)` pairs.
  - V8 convexity alone: **79,026** (-20.86%, 8 empty tasks).
  - **V8 convexity + König bound**: **65,563** (**-34.35%**, **12 empty tasks** — immediately proving `D6-N9-B3-P000..P003-T00` empty in 0.000s and eliminating `t=3`, one-third of `D6-N9-B3-P*-T01`).
- **Exact X x Y Skeleton Collapse for `D6-N9-B3-P*-T01`**: With `t in {4, 5}` and `tau >= 4`, `G[X union Y]` has only **5 isomorphism classes**: `4K2` (t=4), and `5K2`, `P3X+3K2`, `P3Y+3K2`, `P4+2K2` (t=5).

## 3. Local OR-Tools CP-SAT PoC Benchmarks (2-Core VM)

Built compact native CP-SAT model (`cpsat_poc.py` + C++ bitset separator `isep.cpp`, <0.1s separation time).

| Task | Mode | CP-SAT Vars | CP-SAT Ctrs | Build (s) | Wall (s) | Models | Lazy Codegs | I10 Cuts | Status |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| `D6-N9-B3-P002-T01` | `codeg=lazy` | 2,441 | 10,848 | 0.28 | 44.97 | 6 | 202 | 1,536 | `UNKNOWN` |
| `D6-N9-B3-P002-T01` | `codeg=all` | 24,041 | 55,378 | 2.01 | 45.13 | 0 | 0 | 0 | `UNKNOWN` |
| `D6-N9-B3-P002-T01` | `lazy, lin=0` | 2,441 | 10,848 | 0.31 | 29.59 | 4 | 145 | 1,024 | `UNKNOWN` |
| `D6-N9-B3-P000-T01` | `codeg=lazy` | 2,475 | 10,914 | 0.37 | 45.05 | 9 | 239 | 2,304 | `UNKNOWN` |
| `D6-N9-B3-P000-T01` | `codeg=all` | 24,075 | 55,444 | 1.90 | 45.13 | 0 | 0 | 0 | `UNKNOWN` |
| `D8-N8-B0-P000-T01` | `codeg=lazy` | 4,051 | 14,048 | 0.36 | 45.05 | 0 | 0 | 0 | `UNKNOWN` |
| `D8-N8-B0-P000-T01` | `lazy, lin=0` | 4,051 | 14,048 | 0.87 | 30.05 | 0 | 0 | 0 | `UNKNOWN` |

**Verdict on CP-SAT**: 100x–155x smaller model than v7 CNF, but non-incremental CEGAR (learned clauses discarded every cut iteration), weak LP relaxation on triangle-free graphs, and no DRAT/LRAT proof output make **Lean-CNF + Proof-First Kissat/CaDiCaL + SMS** the strictly superior primary engine.

## 4. Lean-CNF + SMS + Proof-First Redesign (`lean_cnf_sms.py`)

| Task | v5/v7 Baseline (Vars / Clauses) | Lean-CNF `static_lex` DRAT (Vars / Clauses) | Reduction | Ultra-Lean `sms` (Vars / Clauses) | Reduction |
|---|---|---|---:|---|---:|
| `D6-N9-B3-P000-T01` | 380,302 / 1,023,840 | **15,605 / 73,326** | **24.4x / 14.0x** | **9,142 / 51,455** | **41.6x / 19.9x** |
| `D6-N9-B3-P002-T01` | 380,268 / 1,023,636 | **15,496 / 72,681** | **24.5x / 14.1x** | **9,033 / 51,000** | **42.1x / 20.1x** |
| `D8-N8-B0-P000-T01` | 425,961 / 1,180,807 | **28,389 / 110,962** | **15.0x / 10.6x** | **21,274 / 86,997** | **20.0x / 13.6x** |

- **Sound Static Symmetry (`static_lex`)**: Maximize `Phi(G) = ((deg(x),deg_Y(x))_X, (deg(y),deg_X(y))_Y, (deg(t),deg_X(t),deg_Y(t))_T, row-major adj(G))` over `S_X x S_Y x S_T`. Every isomorphism class has a lex-maximum representative, and permuting within one block leaves the other two blocks' degree-tuples invariant. 100% DRAT/LRAT verifiable by Kissat + `drat-trim`.
- **SMS (`sms`)**: Omit static lex and run `smsg -v 40 --cnf <file> --initial-partition 1 1 <d-1> <q-1> <40-d-q>` for rapid refutation/cube discovery.

## 5. Full Compute Cost Estimate (231 Unresolved Tasks)

- **v7 Baseline**: 231 tasks x 50 min/wave = **192.5 core-hours/wave** (~12.8 wall-hours at 15 parallel runners), closing ~1–2 tasks/wave (>1,000+ core-hours total).
- **V8 Lean-CNF + Proof-First Kissat + SMS Projection** *(requires controlled 3-task container benchmark first)*:
  - 15x–42x fewer variables (fitting watch lists in L2/L3 cache) + eliminating duplicate CaDiCaL-then-Kissat solving yields an estimated **10x–30x effective throughput gain**.
  - Easy/medium tier (~150 tasks): ~1–5 min each = **5–12 core-hours**.
  - Hard tier (~81 tasks, with König skeleton splitting / adaptive cubes): ~15–60 min each = **20–80 core-hours**.
  - **Total projected**: **~25–95 core-hours** (~2–6 wall-hours at 15 parallel runners).
- **Next Step**: Run a controlled 3-task benchmark (`proof_first_runner.py` on `D6-N9-B3-P000-T01`, `D6-N9-B3-P002-T01`, `D8-N8-B0-P000-T01`, 10 min each) inside `ghcr.io/davidlueng986-alt/math-compute-sat` before authorizing any broader batch.
