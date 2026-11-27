# Ramsey R(3,10) — V8 Agent 4: Tiered Non-Adjacent-Root DAG & Coverage Proof

**Proposal status:** Offline verified mathematical redesign (`dag-v2.json` untouched; no bulk solver run launched). Conditional on published exact tables of $e(3,8,n)$ and $e(3,9,n)$ ([Goedgebeur & Radziszowski 2013](https://arxiv.org/html/1210.5826v4)) and the unconditional `MIN6` singleton elimination from `d678-v6`.

---

## 1. First-Principles Critique of the v7 Adjacent-Root DAG

In v5/v6/v7, every non-9-regular saturated $(3,10;40)$-graph $W$ (degrees in $\{6,7,8,9\}$, 542 surviving Farkas profiles) is rooted at an **adjacent** pair $(0,1) \in E(W)$ of degrees $(d, q)$ with $d \in \{6,7,8\}$ (chosen via weighted Mantel, so $e(H_0) \le 180 - 9d$) and $q \in \{6,7,8,9\}$ (minimum-degree neighbor of $0$).

This adjacent-root choice has **four structural bottlenecks** that explain why 231 of 279 v7 tasks remain OPEN:

1. **Weak core independence bound ($\alpha(T) \le 8$ instead of $\alpha(T) \le 7$):** Because $0 \sim 1$, an independent set in the common antineighborhood $T = V \setminus (N[0] \cup N[1])$ can be extended by *at most one* of $\{0,1\}$. Thus $T \in \mathcal{R}(3,9; 40-d-q)$, which is exponentially larger and looser than $\mathcal{R}(3,8; n_T)$ (e.g., $e(3,9,25)=46$ vs. $e(3,8,25)=65$, a 19-edge gap).
2. **Wide, poorly constrained $e(T)$ windows:** Across the 12 adjacent-root branches, $e(T)$ spans up to 45 edges (e.g., $[35, 80]$ for $(8,9)$), and $n_T \in [23, 28]$ never connects to the tiny $\mathcal{R}(3,8; 27)$ census (477,142 graphs).
3. **Zero direct $I_8$ separation in $T$:** Every cutting plane must be at least a length-36 $I_9$ clause in $H_0$ or $H_1$ (or length-45 $I_{10}$ in $W$), whereas a non-adjacent root pair immediately yields length-28 $I_8$ cuts inside $T$.
4. **No global codegree tightening & fragmented D6/D78/D9 structure:** The 333 degree-6 profiles (61.4% of all D678 profiles) pollute all 12 branches, and D9 is treated by a completely separate non-adjacent-root pipeline (`d9-kaggle-v4`).

---

## 2. Proposed V8 Architecture: Unified Tiered Non-Adjacent-Root DAG

Let $W$ be any saturated (maximal triangle-free) $(3,10;40)$-graph. By the unconditional singleton capacity inequality (`d678-v6`), every vertex has degree in $\{6,7,8,9\}$. For any **non-adjacent** pair $(u, v) \notin E(W)$ of degrees $(d_u, d_v)$ and codegree $c = |N(u) \cap N(v)| \ge 1$ (by saturation):
- Let $S = N(u) \cap N(v)$ ($|S|=c$), $X = N(u) \setminus S$ ($|X|=d_u-c$), $Y = N(v) \setminus S$ ($|Y|=d_v-c$), and $T = V \setminus (N[u] \cup N[v])$.
- **Core order & independence:** $|T| = 38 - d_u - d_v + c \le 27$ and **$\alpha(T) \le 7$** (since $I_8 \subset T$ plus $\{u, v\}$ gives $I_{10}$ in $W$). Thus $T \in \mathcal{R}(3,8; |T|)$ and every $w \in T$ has internal degree $\deg_T(w) \in [|T|-23, 7]$.
- **Exact edge identity:** Because $S \cup X$ and $S \cup Y$ are independent, $e(S, X) = e(S, Y) = 0$ and
  $$e(T) = m - \sum_{w \in S \cup X \cup Y} \deg_W(w) + e(X, Y) \in \big[e(3,8,|T|),\, \lfloor 7|T|/2 \rfloor\big].$$
- **Mandatory $X$–$Y$ matching:** Every $x \in X$ is non-adjacent to $v$ and has no neighbors in $S$, so $\deg_Y(x) = c(x, v) \ge 1$ by saturation; symmetrically $\deg_X(y) \ge 1$ for all $y \in Y$. Hence $e(X, Y) \ge \max(|X|, |Y|)$.

We partition all $(3,10;40)$-graphs into **three disjoint, exhaustive tiers**:

### Tier 1 — Unconditional Degree-6 Elimination ($n_6(W) \ge 1$; 333 profiles)

**Theorem 1 (Degree-6 Inner Weighted-Mantel Cover).** *Every saturated $(3,10;40)$-graph $W$ with $n_6(W) \ge 1$ contains a degree-6 vertex $u$ and a non-adjacent vertex $v \in H_u = W - N[u]$ of internal degree $r = \deg_{H_u}(v) \in \{5, 6, 7\}$ and $W$-degree $q \in \{r+1, \dots, 9\}$ (so $c = q - r \in \{1,2,3,4\}$) such that $T = W - N[u] - N[v]$ satisfies:*
$$T \in \mathcal{R}(3, 8; 32 - r), \qquad e(3, 8, 32 - r) \le e(T) \le 132 - 8r.$$

*Proof.* Pick any vertex $u$ of degree 6 in $W$. Its antineighborhood $H_u = W - N[u]$ has order $h = 33$ and $\alpha(H_u) \le 8$, so $\Delta(H_u) \le 8$ and $\delta(H_u) \ge 33 - 1 - 27 = 5$. By singleton capacity (`d678-v6`), $e(N(u), H_u) \ge 2(33) - 6(4) = 42$, hence $2 e(H_u) \le 9(33) - 42 = 255$, i.e. $118 \le e(H_u) \le 127$. Therefore the deficit $D_H = 8(33) - 2 e(H_u) = 264 - 2 e(H_u) \ge 10 > 0$. Applying Angeltveit's weighted-Mantel blow-up ([arXiv:2401.00392v2, Prop. 2.1](https://arxiv.org/html/2401.00392v2)) to $H_u$ — replacing each $x \in H_u$ by $8 - \deg_{H_u}(x)$ independent copies — yields a triangle-free graph $H_u'$ on $D_H$ vertices. By Mantel's theorem, some vertex of $H_u'$ has degree $\le \lfloor D_H/2 \rfloor = 132 - e(H_u)$, which corresponds to a vertex $v \in H_u$ with $r = \deg_{H_u}(v) \in \{5, 6, 7\}$ and $\epsilon_{H_u}(v) \le 132 - e(H_u)$. Thus
$$e(T) = e(H_u - N_{H_u}[v]) = e(H_u) - 8r + \epsilon_{H_u}(v) \le 132 - 8r.$$
By saturation, $c = \deg_W(v) - r \ge 1$, so $q = r + c \in \{r+1, \dots, 9\}$. $\blacksquare$

This gives **only 9 non-adjacent-root branches** covering all 333 $n_6 > 0$ profiles (replacing all 54+ unresolved v7 tasks across `D6-N6..N9` and removing $n_6>0$ from `D7-*`, `D8-*`):
- $r=5$ ($|T|=27$, $e(T) \in [85, 92]$, 4 branches $q \in \{6,7,8,9\}$): all cores lie inside McKay's complete 477,142-graph $\mathcal{R}(3,8;27)$ census.
- $r=6$ ($|T|=26$, $e(T) \in [73, 84]$, 3 branches $q \in \{7,8,9\}$): 12-edge window.
- $r=7$ ($|T|=25$, $e(T) \in [65, 76]$, 2 branches $q \in \{8,9\}$): 12-edge window.

**Alternative/Hybrid Gluing Fast-Path for Tier 1:** Exact integer Farkas certificates (`verify_v8_dag.py`) prove that **207 of the 333** $n_6 > 0$ profiles force a degree-6 vertex with $e(H_u) \le 121$. By [Angeltveit (2024, Sec. 3.3)](https://arxiv.org/html/2401.00392v2), $|\mathcal{R}(3,9;33, e \le 121)| = 14{,}395$ graphs total (glueable in seconds at ~250 graphs/s/core), and all 333 profiles have $e(H_u) \le 127$ ($\approx 10^7$ graphs vs. $1.55 \times 10^9$ for $\mathcal{R}(3,9;32,e \le 112)$).

---

### Tier 2 — D78 Global Max-$|T|$ Non-Adjacent-Root Cover with Lex-Max Tie-Breaking ($n_6 = 0, n_7 + n_8 > 0$; 209 profiles)

Once Tier 1 excludes $n_6(W) \ge 1$, every remaining non-9-regular graph $W$ has degrees in $\{7, 8, 9\}$ (209 surviving profiles: 190 with $n_7 > 0$ and 19 with $n_7 = 0, n_8 > 0$).

For every non-edge $(x, y) \notin E(W)$, define $|T(x,y)| = 38 - \deg(x) - \deg(y) + c(x,y) \le 27$, and let
$$T^*(W) = \max_{x \not\sim y} |T(x, y)|.$$

**Theorem 2 (D78 Global Max-$|T|$ Lex-Max Cover).** *For every saturated $(3,10;40)$-graph $W$ with $n_6(W) = 0$ and $n_7(W) + n_8(W) > 0$:*
1. $T^*(W) \in \{24, 25, 26, 27\}$ (*never* $\le 23$; certified for all 542 D678 profiles by pure-integer Farkas certificates in `verify_v8_dag.py`).
2. Choosing a non-edge $(u, v)$ attaining $T^*(W)$ that maximizes $(\min(d_u, d_v), \max(d_u, d_v))$ lexicographically in the order $(9,9) > (8,9) > (8,8) > (7,9) > (7,8) > (7,7)$ forces, for **every** non-edge $(x, y)$ in $W$ with $\deg(x) \le \deg(y)$:
   $$c(x, y) \le \begin{cases} \deg(x) + \deg(y) - (39 - T^*) & \text{if } (\deg(x), \deg(y)) >_{\mathrm{lex}} (d_u, d_v), \\ \deg(x) + \deg(y) - (38 - T^*) & \text{otherwise.} \end{cases}$$
3. Out of 23 algebraically valid $(T^*, d_u, d_v)$ branches, exact integer Farkas certification proves $(T^*=24, d_u=7, d_v=8, c=1)$ is **mathematically EMPTY** (171/171 candidate profiles refuted), leaving **22 nonempty branches** covering all 209 D78 profiles with zero gaps.

*Proof of Coverage Completeness.* Every finite non-complete graph $W$ has at least one non-edge; hence the maximum $T^*(W)$ is attained, and among all non-edges attaining $T^*(W)$ a lexicographically maximal degree pair $(d_u, d_v)$ exists. By maximality, no non-edge $(x,y)$ can satisfy $|T(x,y)| > T^*$, nor $|T(x,y)| = T^*$ with $(\deg(x), \deg(y)) >_{\mathrm{lex}} (d_u, d_v)$, giving the exact global codegree cap matrix above. Pure-integer Farkas certificates (`verify_v8_dag.py`) rule out $T^* \le 23$ for all 542 D678 profiles and rule out $(T^*=24, 7, 8)$ for all 209 D78 profiles. $\blacksquare$

### Tier 3 — D9 Unification ($n_6 = n_7 = n_8 = 0, n_9 = 40$; 1 profile)

Applying the exact same $T^*(W)$ criterion to 9-regular graphs gives $d_u = d_v = 9$, $c \in \{3,4,5,6,7\}$, $T^* = 20 + c \in \{23,24,25,26,27\}$, which is **identical** to `jobs/ramsey-r310-d9-kaggle-v4/`.

---

## 3. Quantitative Comparison vs. v7 / v8-Optimization Baseline

All counts computed by `analyze_tiered_v8.cpp` and certified by `verify_v8_dag.py` using the exact v6 Farkas profile set (542 D678 profiles) and the v8 convexity / summed-codegree group filter:

| Metric | v7 Adjacent-Root (raw) | v7 + v8 `group_filter` | **V8 Agent-4 Tiered NA-DAG (Tier 1 + Tier 2)** |
| :--- | :---: | :---: | :---: |
| Core $T$ independence bound | $\alpha(T) \le 8$ | $\alpha(T) \le 8$ | **$\alpha(T) \le 7$** (every branch!) |
| Core order $\|T\|$ | $23 \dots 28$ | $23 \dots 28$ | **$24 \dots 27$** ($n_T=23$ eliminated!) |
| Direct $I_8$ separation in $T$ | No (0 $I_8$ cuts) | No (0 $I_8$ cuts) | **Yes** (length-28 $I_8$ cuts) |
| Global codegree cap | $c \le d_x+d_y-11$ | $c \le d_x+d_y-11$ | **$c \le d_x+d_y-(38-T^*)$ + lex tie-break** |
| Max $e(T)$ window width | 45 edges (`[35,80]`) | 45 edges (`[35,80]`) | **8–12 edges (Tier 1)**, **10–23 edges (Tier 2)** |
| Feasible `(branch, prof, t)` triples | 99,862 | 78,846 | **58,472 (-25.8% vs v8, -41.4% vs v7)** |
| Nonempty branches (D678) | 12 `(d,q)` (279 tasks) | 12 `(d,q)` (271 tasks) | **31** (9 Tier 1 D6 + 22 Tier 2 D78) |
| Mathematically emptied branches | 0 | 0 | **1** (`T*=24, du=7, dv=8` Farkas-refuted) |

### Local CP-SAT PoC Benchmark (`poc_benchmark.py`)

Head-to-head 10-second OR-Tools CP-SAT runs on the exact surviving degree-6 profile $n = (1, 0, 1, 38), m = 178$:

| Encoding | Params | Free edges | Models (10s) | Total cuts | **Length-28 $I_8$ cuts** | Conflicts |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| `v7_adj` | `(d=6, q=9)` | 652 | 13 | 2,489 | **0** | 0 |
| `v7_adj` | `(d=6, q=8)` | 660 | 13 | 2,483 | **0** | 0 |
| `v8_na` (T1) | `(du=6, dv=9, c=4, cap=92)` | 658 | 14 | 3,452 | **896** | 0 |
| `v8_na` (T1) | `(du=6, dv=8, c=3, cap=92)` | 663 | 9 | 2,232 | **576** | **766** |
| `v8_na` (T1) | `(du=6, dv=9, c=3, cap=84)` | 655 | 12 | 2,915 | **768** | 0 |
| `v8_na` (T1) | `(du=6, dv=9, c=2, cap=76)` | 653 | 11 | 2,678 | **704** | 0 |

---

## 4. Files & Reproduction

- `verify_v8_dag.py`: Reproduces all 931/543 profiles and verifies pure-integer Farkas certificates for Theorems 1–2 (`python3 verify_v8_dag.py`, ~80s).
- `analyze_tiered_v8.cpp`: Exact C++20 enumerator for Tier 1 + Tier 2 `(branch, profile, t=e(X,Y))` triples and $e(T)$ ranges.
- `poc_benchmark.py`: Head-to-head OR-Tools CP-SAT benchmark (`v7_adj` vs `v8_na`).
- `v8_dag_verification.json`: Saved verification output (`status: ALL_EXACT_FARKAS_AND_COVERAGE_CHECKS_PASSED`).

## 5. Recommended Next Steps (Before Updating `dag-v2.json`)

1. **Audit & integrate** the Tier 1 + Tier 2 non-adjacent-root SAT encoder with Kissat DRAT proof generation (reusing the `d9-kaggle-v4/d9.py` non-adjacent skeleton, Hall/neighborhood-pattern inequalities, and lex-max symmetry breaking).
2. **Execute Tier 1 Degree-6 Elimination first** — either via the 9 non-adjacent-root SAT branches (with McKay's 477,142 $\mathcal{R}(3,8;27)$ census for $r=5$) or via Angeltveit's fast $(3,9;33)$ gluing extender on the 207 profiles forcing $e(H_u) \le 121$ (14,395 graphs). Closing Tier 1 permanently eliminates 61.4% of all D678 profiles.
3. **Retain existing v7 DRAT proofs** separately until the new V8 non-adjacent-root encoding is independently audited and achieves full parent closure.
