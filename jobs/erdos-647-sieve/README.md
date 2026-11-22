# Erdős #647 sharded witness search (`erdos-647-sieve`)

Searches for an integer $n > 24$ satisfying $\max_{1 \le m < n}(m + \tau(m)) \le n + 2$, equivalently $\tau(n - k) \le k + 2$ for all $1 \le k < n$ ([erdosproblems.com/647](https://www.erdosproblems.com/647), JSP-000525). A single verified witness $n > 24$ closes the problem **YES** (`OPEN -> CLOSED`).

This job starts at the exact July 2026 computational frontier $N_{\text{start}} = 9,174,471,185,880,000,000$ ([bentrd/erdos647-frontier-extension](https://github.com/bentrd/erdos647-frontier-extension), building on [scottdhughes/erdos647-proof-chain](https://github.com/scottdhughes/erdos647-proof-chain)) and scans up to $10^{21}$ by default using `sharded-run`.

## Mathematical reduction and sieve

1. **Exact 786-class wheel ($W = 10,708,457,760$):**
   At startup, `search.cpp` dynamically derives all residue classes modulo
   $$W = 2^5 \cdot 3^2 \cdot 5 \cdot 7 \cdot 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23 = 10,708,457,760$$
   that survive exact divisor-count lower bounds $\tau(n-k) \le k+2$ for $k = 1, \dots, 500$ (valid for all $n \ge 10^{12}$). Exactly **786** residue classes survive (all divisible by $360,360$; density $7.340 \times 10^{-8}$, i.e. 1 in 13.62 million integers — $3.35\times$ tighter than the prior 15,140-progression reduction modulo $61,573,632,120$).
2. **Per-class forbidden offsets ($29 \le p \le 491$):**
   For each class $r \pmod W$, every offset $k \le 600$ with $4 P(r-k) > k+2$ and $M_{\text{exact}}(r-k)\cdot 491^3 < N_{\text{start}}$ forbids $p \mid (n-k)$ for every prime $29 \le p \le 491$ (13 to 23 forbidden residues per prime, average **18.30**).
3. **3-tier word-mask sieve (`O(1)` bitwise AND per 64 candidates):**
   - **Tier 1 (14 primes, $29 \dots 83$):** unrolled 64-bit alive-mask intersection in L1 cache, eliminating $>99.7\%$ of wheel candidates with zero divisions.
   - **Tier 2 (26 primes, $89 \dots 227$):** word-mask intersection using division-free 64-bit reciprocal remainder (`FastMod64`).
   - **Tier 3 (45 primes, $229 \dots 491$):** scalar bitset check on surviving bits using `FastMod64`.
4. **7-prime constellation filter and exact 128-bit verifier:**
   Every sieve survivor is tested for base-2 strong probable primality on all 7 prime-forced cofactors: $n-1$, $(n-2)/2$, $(n-3)/3$, $(n-4)/4$, $(n-6)/6$, $(n-8)/2^{v_2(n-8)}$, and $(n-12)/12$ (using native 64-bit arithmetic below $2^{64}$ and 128-bit CIOS Montgomery arithmetic above $2^{64}$). Any survivor undergoes an exact divisor-count cascade (trial division + Pollard's rho + deterministic Miller-Rabin up to $3.317 \times 10^{24}$) through the exact Superior Highly Composite Number upper bound on $\max_{m < n}\tau(m)$ (e.g., $368,640$ for $n \le 10^{21}$, $860,160$ for $n \le 10^{23}$). Any witness is independently re-verified in pure Python by both `run.py` and `merge.py`.

## Run and interpret results

In GitHub Actions (**Actions** -> **sharded-run** -> **Run workflow**):
- `job`: `erdos-647-sieve`
- `shards`: e.g. `16` (scans $[9.174 \times 10^{18}, 10^{21})$ in ~5–10 minutes per 4-vCPU shard; up to `256` shards supported)
- `timeout_minutes`: `330` (default)
- `max_parallel`: `20`

Optional environment overrides for local or custom runs:
- `ERDOS647_N_START` (default `9174471185880000000`)
- `ERDOS647_N_END` (default `1000000000000000000000`, i.e. $10^{21}$)
- `ERDOS647_BUDGET_SECONDS` (default `18000`, 5 hours per shard)

To reproduce a shard locally:
```bash
ERDOS647_N_START=9174471185880000000 ERDOS647_N_END=9274471185880000000 bash jobs/erdos-647-sieve/run.sh 0 4 out
```

`summary/erdos-647-sieve.json` reports exact shard tiling verification, total wheel candidates tested, sieve funnel counts, the deepest near-miss encountered, and `mathematical_status` (`CLOSED YES` if an independently verified witness is found, otherwise `OPEN`).
