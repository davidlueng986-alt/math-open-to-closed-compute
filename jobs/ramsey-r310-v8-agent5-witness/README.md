# Ramsey R(3,10) V8 — Agent 5 Witness Hunter (40-Vertex Exhaustive Algebraic Scan & C++20 Local Search)

No 40-vertex $(3,10)$-Ramsey witness ($K_3$-free, $\alpha \le 9$) was found. This directory records the C++20 bitmask solvers, exhaustive algebraic exclusions, energy-barrier diagnostics on `seed31002.txt`, and independently verified best candidates.

## Summary of Results

1. **100% Exhaustive Cayley Graph Scan (All 14 Groups of Order 40, degrees $7..9$)**:
   - **1,780,640** triangle-free Cayley graphs enumerated across all 14 isomorphism classes of order-40 groups ($C_5 \rtimes_\phi H$, $|H|=8$).
   - **0 witnesses** ($\alpha \le 9$).
   - **Exact minimum `#I10 = 80`** (9-regular, 180 edges), achieved in 5 non-abelian groups: $C_4 \times D_5$, $D_5 \times C_2^2$, $C_5 \times D_4$, $D_{20}$, and $C_5 \rtimes_{r \mapsto -1, s \mapsto 1} D_4$. Best abelian Cayley graph has `#I10 = 240`.
   - File: `best_cayley.txt` (verified via `jobs/ramsey-r310-wave1/verify.py`: `n=40, e=180, tri=0, I10=80, alpha=10`).

2. **100% Exhaustive $2 \times 20$ Bicirculant Scan ($C_{20}$ acting with 2 orbits of 20, orbit degrees $6..9$)**:
   - Only 67 symmetric sum-free subsets $S \subseteq \mathbb{Z}_{20} \setminus \{0\}$ satisfy $|S| \le 8$ and $\alpha(\text{Cay}(\mathbb{Z}_{20}, S)) \le 9$.
   - **157,280** triangle-free $2 \times 20$ bicirculants exhaustively checked.
   - **0 witnesses**.
   - **Exact minimum `#I10 = 80`** (9-regular, 180 edges, $|S_0|=2, |S_1|=2, |T|=7$).
   - File: `best_2x20.txt` (verified: `n=40, e=180, tri=0, I10=80, alpha=10`).

3. **Block-Circulant Symmetry-Preserving Local Search (`block_circulant_hunter.cpp`)**:
   - $4 \times 10$ ($C_{10}$): **best `#I10 = 70`** (9-regular, 180 edges — strictly beats all Cayley graphs and all $2 \times 20$ bicirculants!). Saved as `best_bc_4x10.txt`.
   - $8 \times 5$ ($C_5$): best `#I10 = 145` (180 edges).
   - $5 \times 8$ ($C_8$): best `#I10 = 160` (180 edges).
   - $10 \times 4$ ($C_4$): best `#I10 = 168` (180 edges).

4. **Strict-TF Multi-Operator Local Search & Energy Barrier Analysis (`witness_hunter_v2.cpp`)**:
   - **Exact 2-switch rigidity audit on `seed31002.txt`** (`#I10 = 10`, 180 edges, 9-regular): out of $\binom{180}{2} \times 2 = 32{,}220$ candidate edge-pair swaps, only **5** are triangle-free, and **all 5 jump from `#I10 = 10` directly to `#I10 = 304`** (+294 barrier).
   - **Exact 2-switch rigidity audit on `best_bc_4x10.txt`** (`#I10 = 70`, 180 edges, 9-regular): **0** valid triangle-free 2-switches exist.
   - **Structural observation on `seed31002.txt`**: its 40 vertices partition into eight 5-vertex blocks where every pair of distinct blocks is joined by a 5-edge matching; 6 blocks are $C_5$ cycles (internal degrees `[2,2,2,2,2]`) and 2 blocks (`20..24` and `35..39`, the 10 vertices appearing in 4 I10-sets each) have internal degrees `[2,2,2,3,1]`.
   - **Intensive 120s 2-thread search** (547,600 exact-I10 iterations with targeted I10-break, 2-switch, 3-switch, and 8–33 edge ruin-and-recreate): `portfolio_fresh` (Exoo-39 lifts, Kalbfleisch-35 lifts, `best_bc_4x10`, fresh random) independently reached **`#I10 = 24`**; `seed31002_deep` confirmed **`#I10 = 10`** as the undefeated minimum.

5. **Soft-Triangle-Penalty Tunneling SA (`soft_tf_hunter.cpp`)**:
   - Relaxed triangle-freeness via a cubic penalty ramp ($20 \to 2520$) to tunnel across the 2-switch rigidity barrier (5.71M exact single-edge evaluations in 60s across 2 threads, 404 triangle-free hits). Best fresh-start triangle-free graph reached `#I10 = 462` (177 edges).

## Files

- `algebraic_scan.cpp`: Exhaustive C++20 scanner for all 14 order-40 Cayley groups and all $2 \times 20$ bicirculants.
- `block_circulant_hunter.cpp`: C++20 orbit-level SA for $4 \times 10$, $5 \times 8$, $8 \times 5$, and $10 \times 4$ block-circulants.
- `witness_hunter_v2.cpp`: C++20 multi-threaded strict-TF solver (2-switch barrier audit, 2-switch, 3-switch, targeted I10-break, ruin-and-recreate).
- `soft_tf_hunter.cpp`: C++20 soft-triangle-penalty tunneling SA solver.
- `results.json`: Machine-readable summary and `verify.py` verification records.
- `best_cayley.txt`, `best_2x20.txt`, `best_bc_4x10.txt`: Independently verified 40x40 adjacency matrices.
