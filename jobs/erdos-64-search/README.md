# Erdős #64 (Erdős–Gyárfás Conjecture) Sharded Search

Searches for a finite simple graph $G$ with minimum degree $\delta(G) \ge 3$ and no simple cycle of length $2^k$ ($k \ge 2$: $4, 8, 16, 32, 64, \dots$). A single verified counterexample closes Erdős Problem #64 (`OPEN -> CLOSED NO`).

## Excluded Regimes (Skipped)

Per 2026 literature, this job avoids already-excluded regimes:
- General graphs with $n \le 40$, cubic graphs with $n \le 48$, and bipartite graphs with $n \le 66$ (Ducoffe & Dumitru, Sep 2026, arXiv:2609.28594).
- Cayley graphs of odd-order groups and finite nilpotent groups (Burkhart, Nov 2026, arXiv:2611.05060).
- Graphs containing 4-cycles (all searched families enforce girth $\ge 5$).

## Search Architecture

1. **Track 1 — Deterministic Sharded Regular Voltage-Graph Lifts (~78M graphs, $n \in [60, 120]$, girth $\ge 5$–$8$)**:
   - Base cubic graphs of girth $\ge 5$: Petersen ($b=10$, girth 5), Heawood ($b=14$, girth 6, bipartite), Flower Snark $J_5$ ($b=20$, girth 5), Dodecahedron ($b=20$, girth 5), McGee ($b=24$, girth 7), Coxeter ($b=28$, girth 7), and Tutte–Coxeter 8-cage ($b=30$, girth 8, bipartite).
   - Fiber groups include non-nilpotent and even-order groups ($A_4, D_6, \text{Dic}_3, S_3$) and cyclic covers ($\mathbb{Z}_3, \mathbb{Z}_4, \mathbb{Z}_6$).
   - Orbit symmetry reduction ($v = u \cdot m + g$, searching only base roots $u \cdot m$) gives an exact $m$-fold speedup on top of 128-bit bitmask meet-in-the-middle cycle checking ($C_4, C_8, C_{16}, C_{32}, C_{64}$).
   - Deterministically partitioned via `idx = SHARD + k * SHARDS`.
2. **Track 2 — Soft-Barrier Tunneling Simulated Annealing (Asymmetric Odd Near-Cubic & Cubic Graphs)**:
   - Targets odd near-cubic graphs ($n \in \{41, 43, 45, 47, 49, 51, 55, 59, 63\}$, with $n-1$ degree-3 vertices and one degree-4 vertex — unexplored down to $n=41$) and cubic graphs ($n \in \{50, 52, 54, 56, 58, 60, 62, 70\}$).
   - Uses degree-preserving 2-switches strictly forbidding $C_4$, soft-barrier $C_8 \le 3$ tunneling, uncapped exact $C_{16}$ gradient, and cyclic reheating across 4 OpenMP threads per shard.

## Run & Reproduce

In GitHub Actions (**Actions → sharded-run → Run workflow**):
- `job`: `erdos-64-search`
- `shards`: `16` to `256` (at 16+ shards, Track 1 exhausts all ~78M lifts in seconds per shard; increase `ERDOS64_SA_SECONDS` for deeper Track 2 campaigns).
- `timeout_minutes`: `30` (default budgets: `ERDOS64_LIFT_SECONDS=3600`, `ERDOS64_SA_SECONDS=300`).

Local reproduction of shard 0 of 16:
```bash
ERDOS64_LIFT_SECONDS=10 ERDOS64_SA_SECONDS=5 bash jobs/erdos-64-search/run.sh 0 16 out
```

If any shard finds a counterexample, both `run.py` and `merge.py` independently verify $\delta(G) \ge 3$ and the absence of all $2^k$-cycles in pure Python and emit `witness.json`.
