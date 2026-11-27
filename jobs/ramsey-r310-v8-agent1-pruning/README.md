# Ramsey R(3,10) — Agent 1 Exact Integer Structural Pruning & Certificates

Offline, 100% exact-integer pruning engine and independent zero-solver verifier for the 40-vertex saturated triangle-free Ramsey $R(3,10)$ exclusion framework ($\alpha(W) \le 9$, degrees in $\{6, 7, 8, 9\}$). No v7 files or GitHub Actions workflows are modified; no floating-point-only exclusion is ever accepted.

## Exact Measured Results (2026-11-27)

Exact reproduction of both the v6 profile partition (931 $\to$ 543 surviving profiles, 388 Farkas-excluded, 48 $\to$ 44 nonempty D678 bands) and the v8 baseline (`experiment-2026-11-27.json`: 99,862 $\to$ 79,026 total pairs; 96,795 $\to$ 77,563 unresolved pairs; 8 empty tasks) is verified to the exact integer.

| Metric | v6 Baseline | v8 (`group_filter.py`) | **Agent 1 (Exact Integer)** | Reduction vs v6 | Further Reduction vs v8 |
|---|---:|---:|---:|---:|---:|
| Total `(task, profile, t)` pairs (279 v7 tasks) | 99,862 | 79,026 | **38,065** | **-61.88%** (-61,797) | **-51.83%** (-40,961) |
| Unresolved `(task, profile, t)` pairs (231 tasks) | 96,795 | 77,563 | **38,065** | **-60.67%** (-58,730) | **-50.92%** (-39,498) |
| Tasks with reduced `(profile, t)` tables | — | 177 / 279 | **275 / 279** (267 vs v8) | — | — |
| Provably empty v7 tasks (of 279) | 0 | 8 | **61** | +61 | +53 |
| Already CNF-certified tasks independently closed | 0 / 48 | 8 / 48 | **48 / 48 (100%)** | +48 | +40 |
| **Newly closed unresolved v7 tasks (of 231)** | 0 | 0 | **13** (14 vs 232 start) | **231 $\to$ 218** | **+13 closed** |

### 13 Newly Closed Unresolved v7 Tasks (Pure Exact Integer Certificates)

All 47 tasks certified in v7 pilot+rollout plus the 48th task (`D8-N8-B0-P000-T01`) certified in continuation are 100% independently proved empty by pure integer arithmetic, together with **13 brand-new unresolved v7 tasks**:

- `D7-N6-B3-P000-T01`, `D7-N6-B3-P001-T01`, `D7-N6-B3-P002-T01`, `D7-N6-B3-P003-T01`, `D7-N6-B3-P004-T01` (5 tasks)
- `D8-N6-B3-P000-T01`, `D8-N6-B3-P001-T01`, `D8-N6-B3-P002-T01`, `D8-N6-B3-P003-T01`, `D8-N6-B3-P004-T01` (5 tasks)
- `D8-N7-B0-P000-T01`, `D8-N7-B0-P001-T01`, `D8-N7-B0-P002-T01` (3 tasks)

### D9 (`n = (0, 0, 0, 40), m = 180`) Adjacent-Edge Bounds

For any adjacent edge $\{0, 1\}$ in a 9-regular 40-vertex triangle-free graph with $\alpha \le 9$ ($n_X = n_Y = 8$, $n_T = 22$, $s_X = s_Y = 72$):
- $t = e(X, Y) \ge 9 + 9 - 11 = 7$
- $x_T, y_T \ge 2(22) - 8(10 - 9) = 36 \implies t \le 72 - 8 - 36 = 28$

## First-Principles Mathematical Derivations (100% Sound)

Let $W$ be a saturated triangle-free 40-vertex graph with $\alpha(W) \le 9$ and degrees in $\{6, 7, 8, 9\}$. For adjacent roots $0, 1$ of degrees $d, q$, let $X = N(0)\setminus\{1\}$ ($n_X = d-1$), $Y = N(1)\setminus\{0\}$ ($n_Y = q-1$), and $T = V \setminus (N[0] \cup N[1])$ ($n_T = 40-d-q$). Both $X$ and $Y$ are independent, and $t = e(X, Y)$, $x_T = s_X - n_X - t$, $y_T = s_Y - n_Y - t$.

1. **Cross-edge independent-set lower bound ($t \ge \max(0, d + q - 11)$):**
   Let $Y_0 = \{w \in Y : \deg_X(w) = 0\}$. Since $X$ and $Y_0$ are independent with no edges between them, $X \cup Y_0$ is an independent set of size $(d - 1) + |Y_0| \le 9 \implies |Y_0| \le 10 - d$. Thus at least $n_Y - (10 - d) = d + q - 11$ vertices in $Y$ have $\deg_X(w) \ge 1$, giving $t \ge d + q - 11$. Symmetrically $|X_0| \le 10 - q$.

2. **Rooted singleton lower bounds on $x_T, y_T$ (sharp new upper bound on $t$):**
   For each $a \in X$, let $S_a = \{w \in T : N_X(w) = \{a\}\}$. Because $W$ is triangle-free, $S_a$ is independent; by definition $S_a$ has no edges to $X \setminus \{a\}$ or to $1$ (since $T \cap N(1) = \emptyset$), and $1$ has no edges to $X \setminus \{a\}$ (since $N(0) = \{1\} \cup X$ is independent). Hence $S_a \cup (X \setminus \{a\}) \cup \{1\}$ is an independent set of size $|S_a| + d - 1 \le 9 \implies |S_a| \le 10 - d$. Summing over $a \in X$ gives $|\{w \in T : \deg_X(w) = 1\}| \le n_X(10 - d)$. Since saturation forces $\deg_X(w) \ge 1$ for every $w \in T$,
   $$x_T \ge 2 n_T - n_X(10 - d), \qquad y_T \ge 2 n_T - n_Y(10 - q).$$

3. **Shared-root codegree caps on $Y$ and $X$:**
   Every $w \in Y$ is non-adjacent to $0$ and already shares root $1 \in N(0) \cap N(w)$. By $R(3, 8) = 28$, $\text{codeg}_W(0, w) = 1 + \deg_X(w) \le \deg(w) + d - 11$, so $\deg_X(w) \le \min(n_X, \deg(w) + d - 12, \deg(w) - 1)$. Symmetrically, for $w \in X$, $\deg_Y(w) \le \min(n_Y, \deg(w) + q - 12, \deg(w) - 1)$.

4. **Exact water-filling degree-capped & singleton-capped convexity:**
   Because $\binom{d+1}{2} - \binom{d}{2} = d$ is strictly increasing in $d$, water-filling from `lb` upward subject to heterogeneous vertex caps $d_w \le \text{cap}_w$ simultaneously minimizes $|\{w : d_w = \text{lb}\}|$ and $\sum \binom{d_w}{2}$. Applying this exact integer minimum to $(T, \text{lb}=1, \text{max\_ones}=n_X(10-d))$ and $(Y, \text{lb}=0, \text{max\_zeros}=10-d)$ sharpens the V8 pair-codegree convexity inequality $\sum_{T \cup Y} \binom{\deg_X(w)}{2} \le (n_X - 1) s_X - 12 \binom{n_X}{2}$ (and symmetrically for $Y$).

## Negative / Tightness Findings on Global Profile LPs

- **1-Vertex ILP integrality gap = 0:** Solving the exact integer feasibility problem for the v6 1-vertex system on all 543 surviving profiles via OR-Tools CP-SAT confirms that every one of the 543 surviving profiles admits an integer vertex-type solution (0 additional global profile exclusions).
- **Global Joint Vertex-Edge LP + $C_4$ coupling & nested $e(3,8)$ bounds:** Tested across boundary (`m >= 174`, `n6 >= 8`) and lowest-`m` (80 profiles) regimes, plus $T$-distribution $(d_X, d_Y)$ coupling with $X$-$Y$ nonedge codegree bounds and higher-order $T_B$ Ramsey bounds; these yield 0 additional exclusions beyond the 4 exact inequalities above. All 44 nonempty D678 bands remain nonempty (each has at least one surviving `(profile, t)`).

## Reproduction & Independent Verification

```bash
# Run full selftest, v6 Farkas generation, 279-task screening, and certificate export (~42s)
OPENBLAS_NUM_THREADS=1 python3 agent1_pruner.py --out-dir out

# Run independent zero-solver pure-integer verifier (stdlib only, ~2.4s)
python3 verify_agent1.py --dir out
```

## Files

- `agent1_pruner.py` — Exact integer pruner, selftest suite, and certificate generator.
- `verify_agent1.py` — Independent pure-integer verifier (Python stdlib only; verifies all 388 v6 Farkas certificates and all 61 closed v7 tasks / 406 profile instances).
- `agent1_pruning_summary.json` — Exact v6 / v8 / Agent 1 benchmark metrics and SHA-256 certificate digest.
- `agent1_closed_tasks_certificates.json` — Independently verifiable exact-integer refutation records for all 61 provably empty v7 tasks.
