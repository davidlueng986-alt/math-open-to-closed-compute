# Erdős #287 (JSP-000244) — Unconditional Prime-Power & Proth-Certified Covering Chain

This job constructs and independently verifies a **zero-gap unconditional lower bound** on the largest denominator $n_k$ of any hypothetical counterexample to Erdős Problem #287:
$$\sum_{i=1}^k \frac{1}{n_i} = 1, \quad 1 < n_1 < \dots < n_k, \quad \max_{1 \le i < k} (n_{i+1} - n_i) \le 2.$$

> **Scope note:** Even a 1,000+ digit unconditional lower bound does **not** prove Erdős #287 globally (it remains `OPEN` unless either a finite counterexample or a uniform theorem for all $n_k$ is found).

## Mathematical Obstructions

1. **Generalized Prime-Power $p$-adic Exclusion (Theorem 1):**
   Let $B = n_k$ and let $q = p^a \parallel x$ with $p^{a+1} > B$, $m = \lfloor B/q \rfloor$, $L_m = \operatorname{lcm}(1, \dots, m)$, and $N_m = \sum_{h=1}^m L_m / h$. If $p > N_m$, then no multiple $hq \le B$ can appear in $S$ (since multiplying $\sum_{n \in S} 1/n = 1$ by $q L_m$ and reducing mod $p$ forces $0 < \sum_{h \in H} L_m/h \le N_m < p$ to be divisible by $p$, impossible). More sharply, for $m < p \le N_m$, $x = hq$ is forced omitted unless some subset $H \subseteq \{h_{\min}, \dots, m\}$ containing $h$ has $\sum_{j \in H} L_m/j \equiv 0 \pmod p$.

2. **Adjacent Forced-Omission Interval Killer (Theorem 2):**
   Since $\sum_{n=x}^B \frac{1}{n} < \ln\left(\frac{B}{x-1}\right)$, whenever $B \le \lfloor e(x-1) \rfloor$ we must have $n_1 < x$. If also $B \ge x + 2$, then both $x$ and $x + 1$ lie strictly inside $(n_1, n_k)$.
   In particular, for any prime pair $(p', p)$ with $p' \ge 139$ and $p = 2p' - 1$ both prime, $p > N_2 = 3$ and $p' > N_5 = 137$, so both $x = p$ and $x + 1 = 2p'$ are forced omitted for every
   $$B \in \big[p + 2, \; \lfloor e(p - 1) \rfloor\big].$$
   Each single pair kills a multiplicative factor of $e \approx 2.71828$ of $B$ values.

3. **Independently Shardable Proth-Certified Chain:**
   For each exponent $n \in [n_{\min}, n_{\max}]$, we search $k \equiv 3 \pmod 6$ inside a fixed window $[K_{\text{lo}}, K_{\text{hi}}]$ with $K_{\text{hi}} / K_{\text{lo}} \le 1.35 < e/2$ and $K_{\text{hi}} < 2^{n_{\min}}$, using a chunked mod-6 wheel sieve followed by **Proth's Theorem (1878)**: if $a^{(N-1)/2} \equiv -1 \pmod N$ for $N = k \cdot 2^m + 1$ with $k < 2^m$, then $N$ is unconditionally prime.
   Because $2 \cdot (K_{\text{hi}} / K_{\text{lo}}) \le 2.70 < e$, consecutive exponents $n$ and $n+1$ overlap **unconditionally and independently** across shards.

## Running on GitHub Actions

Use **Actions → `sharded-run` → Run workflow**:
- `job`: `erdos-287-sieve`
- `shards`: `32` (or up to `256`; default range $n \in [33, 3322]$ covers all $n_k$ up to **$10^{1009}$** with GMP on 4-vCPU runners in a few minutes per shard)
- `timeout_minutes`: `120`
- `max_parallel`: `20`

Local reproduction (2-shard test on a smaller range):
```bash
ERDOS287_N_MIN=33 ERDOS287_N_MAX=60 bash jobs/erdos-287-sieve/run.sh 0 2 out/shard-0
ERDOS287_N_MIN=33 ERDOS287_N_MAX=60 bash jobs/erdos-287-sieve/run.sh 1 2 out/shard-1
SHARDS=2 python3 jobs/erdos-287-sieve/merge.py out summary
```
