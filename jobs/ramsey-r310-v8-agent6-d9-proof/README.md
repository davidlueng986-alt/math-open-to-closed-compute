# Ramsey R(3,10) — Agent 6: D9 Algorithmic Breakthrough & V8 Proof-First Certificate Pipeline

**Status**: Offline algorithmic R&D & local benchmarks complete; **no bulk GitHub Actions launched** (per `milestone-2026-11-27.md`).

## 1. D9-C7 First-Principles Analysis & Local Benchmarks

In D9-C7 ($c = 7$, 9-regular triangle-free 40-vertex graph with $\alpha \le 9$ and max nonedge codegree $c = 7$):
- $|S| = 7$, $|X| = 2$, $|Y| = 2$, $|T| = 27$.
- $e(T) = 81 + e(X, Y) \ge e(3,8,27) = 85$ and $e(X, Y) \le 4$ **force $e(X, Y) = 4$ ($K_{2,2}$) and $e(T) = 85$**, restricting $T$ to the **4** isomorphism classes of $(3,8; 27, 85)$ in McKay's `r38_27.g6.gz` census (477,142 graphs total).
- Fixing $T$ collapses the entire 40-vertex graph to an **11 × 27 Boolean matrix** $M[r][t]$ (**297 variables**): 7 independent 7-sets in $T$ (rows $S$) and 4 independent 6-sets in $T$ (rows $X, Y$).

### New Proved Necessary Constraints (Missing or Bloated in Kaggle v4 `d9.py`)
1. **Exact $X/Y$ Disjointness**: Since $G[X,Y] = K_{2,2}$, $U_X \cap U_Y = \emptyset$ where $U_X = N_T(x_1) \cup N_T(x_2)$ and $U_Y = N_T(y_1) \cup N_T(y_2)$.
2. **Exact $S$-Domination Theorem**: Every $t \in T$ must touch both $A = S \cup X$ and $B = S \cup Y$ (by $\alpha \le 9$). Since $U_X \cap U_Y = \emptyset$, **every $t \in T$ must have $d_S(t) \ge \max(1, (9 - d_T(t)) - 2)$** (e.g., $d_S(t) \ge 2$ for degree-5 vertices in $T$, and $d_X(t) + d_Y(t) \le 1$ for degree-7 vertices in $T$).
3. **Exact $X/Y \to T$ Saturation**: For $x \in X, t \in T$: $M[x][t] \lor uy[t] \lor \bigvee_{u \in N_T(t)} M[x][u]$ (and symmetric for $Y$).
4. **100% Redundancy of Nonadjacent $T$-Pair Codegree Counters**: On our real $(3,8; 27, 85)$ graph (`ZI_eD@@EOCG@dGO?OBGCeC?GRDC?gQW?yOCOI@a?gQCd@WOIGH_@g?L@oh??`), **0 / 266** nonadjacent $T$-pairs satisfy $\text{codeg}_T(u,v) + \min(9 - d_T(u), 9 - d_T(v)) > 7$. Kaggle v4 `d9.py` generated sequential counters for all 673 non-edge pairs anyway.
5. **Targeted Hall $b=1, 2$ + Static $I_7(T)$ Hitting-Set Encoding**:
   - Replaces `d9.py`'s 1,004 Hall subsets ($k = 0..7$, ~30,120 `AND` gates) with exact Hall $b=1$ private-neighbor bounds (1 clause per $(s,t)$), Hall $b=2$ bounds, and exact $I_7(T)$ hitting-set constraints (for every $W \in \mathcal{I}_7(T)$, at most 2 rows of $A = S \cup X$ and at most 2 rows of $B = S \cup Y$ may miss $W$).

### Honest Local Benchmark Findings (Real $(3,8; 27, 85)$ Graph)
We generated and independently verified a real $(3,8; 27, 85)$ graph locally (27 vertices, 85 edges, degree distribution `{5:4, 6:11, 7:12}`, triangle-free, $\alpha \le 7$) and measured:
- $|\mathcal{I}_7(T)| = 750$, $|\mathcal{I}_6(T)| = 2,833$, with **99.1%** of $\mathcal{I}_7(T)$ pairs satisfying $|I_a \cap I_b| \le 5$ and 130–266 sets per vertex.
- **Why naive C++ bitmask DFS (`d9c7_gluer.cpp`) does NOT finish in seconds**: With branching factor ~130 at depth 0 over 750 $\mathcal{I}_7(T)$ sets, pure backtracking exceeds $10^7$ nodes and times out at 30s on 1 core.
- **Why V8 Compact 297-var CNF + Kissat (`d9c7_compact_cnf.py`) is the right GitHub Actions weapon**:
  - Shrinks `d9.py`'s ~65,000+ vars / ~250,000+ clauses down to **16,535 vars / 34,930 clauses** (`base + b1`), **23,885 vars / 49,350 clauses** (`+ b2`), or **56,135 vars / 114,600 clauses** (`+ all 750 I7` statically baked in).
  - Runs directly in **single-pass Proof-First Kissat + `drat-trim -L` + `lrat-check`** on `math-compute-sat` (4 parallel jobs for the 4 cores of `r38_27.g6.gz`), emitting independently verified DRAT/LRAT certificates with zero double-solving!

## 2. D9-C6 Exact Skeleton Orbit Decomposition (`d9c6_skeletons.py`)
- All $2^9 - 1 = 511$ nonempty $3 \times 3$ bipartite skeletons $G[X,Y]$ ($1 \le e(X,Y) \le 9$, $e(T) \in [73, 81]$) collapse under $S_3(X) \times S_3(Y) \times \mathbb{Z}_2$ to **exactly 25 isomorphism classes** (`D9-C6-S00`..`D9-C6-S24`).
- Fixing each orbit locks all $d_T(x), d_T(y)$, tightens intra-$X$/$Y$ $T$-codegree caps to $5 - |N_Y(x_1) \cap N_Y(x_2)|$ (down to 2), and forces full $S$-domination at $e(X,Y)=9$.

## 3. V8 Proof-First Certificate Architecture (`V8_PROOF_FIRST_SPEC.md`, `v8_proof_first_worker.py`)
- Eliminates v7 `worker.py`'s CaDiCaL $\to$ Kissat double-solving waste via **Phase 1 (bounded cut separation) $\to$ Phase 2 (single-pass frozen-CNF Kissat DRAT + `drat-trim -L` + `lrat-check`)**.
- Directly resolves `D8-N8-B0-P000-T01`'s 12 `UNSAT_UNCERTIFIED` leaves via priority Phase 2 scheduling + clean cube splitting on timeout.
- Preserves all 48 existing v7 certified tasks immutably under `encoding_version="v7-base"` with an explicit offline encoding-equivalence and LRAT-upgrade audit protocol.

## Files in this Directory
- `d9c7_compact_cnf.py` — V8 compact 297-var D9-C7 CNF encoder, `r38_27.g6.gz` 4-core extractor, proof-first Kissat/DRAT/LRAT runner, and exhaustive `--selftest`.
- `d9c7_gluer.cpp` — C++20 bitmask $(3,8;27,85)$ verifier, $\mathcal{I}_7/\mathcal{I}_6$ enumerator, and exact gluing solver PoC.
- `d9c6_skeletons.py` — Exact 25-orbit $3 \times 3$ bipartite skeleton classifier for D9-C6 (`--selftest`).
- `V8_PROOF_FIRST_SPEC.md` — Full V8 proof-first certificate architecture & legacy 48-task audit specification.
- `v8_proof_first_worker.py` — Reference V8 proof-first cube scheduler & Kissat/DRAT/LRAT runner (`--selftest`).
- `benchmarks_local_2026-11-27.json` — Exact local VM benchmark measurements.
