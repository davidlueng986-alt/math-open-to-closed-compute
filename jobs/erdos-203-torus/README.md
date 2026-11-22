# `erdos-203-torus` — Erdős Problem #203 2D Quotient-Torus Covering Search

**Problem ([erdosproblems.com/203](https://www.erdosproblems.com/203)):** Is there an integer $m \ge 1$ with $\gcd(m, 6) = 1$ such that $2^k 3^\ell m + 1$ is composite for all $k, \ell \ge 0$?

## Mathematical Background & 2026 Frontier

For each prime $p \ge 5$, let $H_p = \langle 2, 3 \rangle \le (\mathbb{Z}/p\mathbb{Z})^\times$ and $e_p = |H_p| = \operatorname{lcm}(\operatorname{ord}_p(2), \operatorname{ord}_p(3))$. The exponent lattice $L_p = \{(k, \ell) \in \mathbb{Z}^2 : 2^k 3^\ell \equiv 1 \pmod p\}$ has index $e_p$ and is given by a single linear congruence $u_p k + v_p \ell \equiv 0 \pmod{e_p}$ with $\gcd(u_p, v_p, e_p) = 1$. Any finite covering of $\mathbb{Z}^2$ by cosets $C_p(r_p) = \{u_p k + v_p \ell \equiv r_p \pmod{e_p}\}$ immediately yields an explicit CRT witness $m$ ($\gcd(m, 6) = 1$) closing Erdős #203 = YES.

- **Prior 2026 exclusions:** Pure covering systems are proved impossible for all periods $N \le 65{,}520$ and all divisors of $110{,}880, 166{,}320, 221{,}760, 332{,}640, 720{,}720$ ([Oct 12, 2026](https://erdosproblemaday.com/day/203-no-covering-system-with-period-up-to-30000); [Oct 14, 2026](https://erdosproblemaday.com/day/203-the-quotient-lemma-lines-close-the-open-pools)).
- **Local pre-deployment narrowing:**
  - Exact CP-SAT line-projection with power-residue constraints rules out the previously open perfect-power cases ($m = t^{N_0}$) at $N = 55{,}440$ ($\max\min W \le 0.754$) and $N = 65{,}520$ ($\le 0.839$).
  - At $N = \operatorname{lcm}(1..17) = 12{,}252{,}240$, the 5–7 cut breaks ($B_{57}(\bmod 60) = 1.0168 > 1$ on 192 primes $\le 20\text{M}$), though CP-SAT on $M = 60$ still bounds $\min W \le 0.9625 < 1$.
  - $N = \operatorname{lcm}(1..23) = 5{,}354{,}228{,}880$ is the first smooth period surviving 1D slope-1 line projection ($\min W = 1.0174$ on $M = 420$), while failing 2D $(\mathbb{Z}/60\mathbb{Z})^2$ ($\min W \approx 0.350$).
  - Our C++17 solver achieved the first 2D quotient-torus feasibility (`deficient_cells = 0`, `min_W >= 1.0`) at **$M_0 = 60$ for $K = 47$** (`min_W = 1.0224`) and **$M_0 = 120$ for $K = 59$** (`min_W = 1.0221`), and reached `min_W = 0.9300` (`3,604 / 129,600` deficient cells) on **$M_0 = 360$ at $K = 71$**.

## Algorithm (`search.cpp`)

On a quotient torus $(\mathbb{Z}/M_0\mathbb{Z})^2$ for smooth period $N = \operatorname{lcm}(1..K)$:
1. Primes with $e_p \mid M_0$ completely kill their cosets ($M_0^2 / e_p$ cells).
2. Remaining primes ($e_p \nmid M_0$) deliver exact fractional intensity $w_p = g_p / e_p$ ($g_p = \gcd(e_p, M_0)$) to their $M_0^2 / g_p$ projected cells.
3. Zero-table $O(1)$ stride iteration + active deficient-cell list (`def_list`) acceleration runs multi-start OpenMP randomized greedy + $L_4/L_8/L_{16}$ minimax coordinate descent + perturbation kicks.
4. Every shard runs a built-in **$N = 5040$ positive control** (31 primes, $\sum 1/e_p = 143/140$), checks every coset cardinality $= M_0^2 / g_p$, and independently re-verifies the best witness from raw congruences.

## Running on GitHub Actions

1. Open **Actions** → **sharded-run** → **Run workflow**.
2. Set `job` = `erdos-203-torus`, `shards` = `8` to `256`, `timeout_minutes` = `330`, `max_parallel` = `20`.
3. By default, shards cycle deterministically across `(K, M0)` frontier targets `(71, 360)`, `(73, 360)`, `(79, 360)`, `(83, 360)`, `(79, 720)`, `(83, 720)`, `(89, 720)`, `(97, 720)` with `prime_limit = 50,000,000` and a 4.5-hour soft cutoff (`ERDOS203_TIME_LIMIT=16200`).
4. Optional environment overrides: `ERDOS203_K`, `ERDOS203_M0`, `ERDOS203_LIMIT`, `ERDOS203_RESTARTS`, `ERDOS203_SWEEPS`, `ERDOS203_KICKS`, `ERDOS203_TIME_LIMIT`.
