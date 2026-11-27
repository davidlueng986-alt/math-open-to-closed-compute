# V8 Proof-First Certificate Architecture Specification (`math-compute-sat`)

## 1. Root-Cause Audit of v7 `worker.py`

Direct inspection of `jobs/ramsey-r310-cubes-v7/worker.py` (commits `ab732737` and `6b513630`) and `jobs/ramsey-r310-repair-v3/repair.py` (`10c3bc00`) reveals three structural bottlenecks that caused low certified-terminal yield and `UNSAT_UNCERTIFIED` leaves:

1. **CaDiCaL $\to$ Kissat Double-Solving Waste (`worker.py` lines 147–188)**:
   - `worker.py` keeps one warm incremental `Cadical195` instance across all cubes (`sol.solve_limited(assumptions=cube)` in 25k-conflict slices up to `cube_seconds=180`).
   - When `Cadical195` returns `False` (UNSAT), its derivation and learned clauses are **discarded**. `worker.py` then serializes `f2 = base + cutclauses + [[v] for v in cube]` to `leaf.cnf` and invokes `v5.repair.proof(f2, dest, budget)`, launching a **cold-start `kissat`** from scratch.
   - Because `budget = min(a.proof_seconds, max(0, (rem - 10) // 2))` splits the remaining wall clock in half (giving `kissat` and `drat-trim` each `budget` seconds), hard cubes that CaDiCaL solved only via warm sibling-cube learned clauses frequently time out in cold-start Kissat.
2. **Root Cause of `D8-N8-B0-P000-T01`'s 12 `UNSAT_UNCERTIFIED` Leaves**:
   - Warm incremental CaDiCaL refuted those 12 leaves, cold-start Kissat timed out within 240s, and `worker.py` recorded `UNSAT_UNCERTIFIED` (or, when `len(cube) < max_depth`, immediately split the already-UNSAT leaf into two brand-new `OPEN` children `k+'0'` and `k+'1'`, throwing away the refutation signal!).
3. **DRAT-Only Replay Overhead on Resume**:
   - On every resume, `worker.py` re-runs `drat-trim` on every previously `CERTIFIED_UNSAT` leaf. `drat-trim` performs backward propagation search, whereas `lrat-check` (already compiled and installed in `ghcr.io/davidlueng986-alt/math-compute-sat` at `/usr/local/bin/lrat-check`) verifies LRAT certificates in linear time $O(|\text{proof}|)$ — typically 10–50× faster and 3–10× smaller on disk after trimming!

---

## 2. V8 Proof-First Two-Phase Cube Pipeline

Every cube `k` executes under a strict **Proof-First** discipline using the exact binaries pinned in `containers/sat/Dockerfile` (`kissat` rev `8af8e56f`, `drat-trim` + `lrat-check` rev `2e3b2dc0`, `Cadical195` via PySAT):

### Phase 1 — Bounded Cut-Saturation (Model-Rich Cubes Only)
- **Skip condition**: If node `k` has `status == 'UNSAT_UNCERTIFIED'` (e.g., all 12 leaves of `D8-N8-B0-P000-T01`), **skip Phase 1 completely** and go directly to Phase 2.
- Otherwise, run incremental `Cadical195` on `cube` ONLY to harvest universal $I_{10}$ cuts while models are still being produced.
- **Zero-Model Handoff Trigger**: As soon as `Cadical195` hits a **single zero-model conflict slice** (e.g., `25,000` conflicts with 0 new models, ~1–3 seconds), **STOP `Cadical195` immediately**. Do not let an uncertified incremental solver spend 180 seconds proving UNSAT without emitting a proof.

### Phase 2 — Single-Pass Proof-First Frozen CNF (`kissat` $\to$ `drat-trim -L` $\to$ `lrat-check`)
1. Freeze `F_k = base + cutclauses[:cut_count] + [[v] for v in cube]` to `leaf.cnf` and compute `cnf_sha256`.
2. Run **standalone `kissat`** directly with native binary DRAT emission:
   ```bash
   kissat --time=<solve_budget> leaf.cnf leaf.drat
   ```
3. Handle the three exact exit codes:
   - **Exit 20 (UNSAT — zero re-solving!)**:
     - `leaf.drat` is **already generated** from the exact solve pass.
     - Run `drat-trim leaf.cnf leaf.drat -L leaf.lrat` to verify AND emit a trimmed LRAT proof.
     - Run `lrat-check leaf.cnf leaf.lrat` as an independent linear-time second checker.
     - Persist `leaf.lrat.gz` (fallback `leaf.drat.gz` if LRAT exceeds size cap), record `cnf_sha256`, `drat_sha256`, `lrat_sha256`, `solve_seconds`, `verify_seconds`, `drat_bytes`, `lrat_bytes`, `cut_count`, mark node `CERTIFIED_UNSAT`, and unlink `leaf.cnf`.
   - **Exit 10 (SAT)**:
     - Parse the `v ...` assignment directly from `kissat.log`, verify the 40-vertex graph, and separate $I_8/I_9/I_{10}$ cuts.
     - If no $I_{10}$ exists: run independent `jobs/ramsey-r310-wave1/verify.py`, save `witness.txt` + `witness-check.json`, mark `VERIFIED_WITNESS`, and halt.
     - If $I_{10}$ cuts are found: append to `cuts.jsonl`, return to Phase 1.
   - **Exit 0 / Timeout (UNKNOWN)**:
     - Never leave a dead `UNSAT_UNCERTIFIED` leaf stuck at the same cube!
     - Split cube `k` into complementary children `k+'0'` (`cube + [-var]`) and `k+'1'` (`cube + [var]`) using propagation/conflict-aware branching on cross-edges / high-degree structural variables, and persist both children atomically.

---

## 3. Auditing the 48 Existing v7 Certified Tasks (Zero Re-Solving, Zero Coverage Loss)

The 48 v7 certified tasks (47 from pilot `45713450151` / rollout `45715254768` + 1 from continuation `45936075262`) are **immutable assets**. V8 enforces strict encoding isolation:

1. **Encoding Version Tagging**:
   - Every task checkpoint carries `encoding_version` (`"v7-base"` vs `"v8-group-filter"` vs `"v8-d9c7-compact"`) and `base_sha256`.
   - Legacy `"v7-base"` certified tasks are **never invalidated or re-solved** when V8 introduces tighter base encodings for the remaining 231 unresolved D678 tasks.
2. **Offline Two-Tier Audit Protocol for the 48 v7 Tasks**:
   - **Plan & Partition Audit**: Verify `profile_cert.json` + `plan.json` exact product coverage of `(m, profile, t)` against `d678-v5` and `v6` certificates (already verified by `continuation.py`).
   - **Base Encoding Soundness Audit**: Independently audit every constraint family in `v5.formula(d, q, band)` + `z.brange(XY, tlo, thi)` (two-root skeleton, exact degree totalizers, profile selector disjunction, dual edge bounds, degree-aware nonedge codegree caps, deficit-weighted neighbor sums, Hall $b=1..4$ neighborhood bounds, and lex-max ordering within $X, Y, T$).
   - **Cut & Proof Replay Audit**: For each of the 48 tasks, verify every line in `cuts.jsonl` is a valid 10-vertex subset of `{0..39}`, reconstruct `leaf.cnf` from `base + cutclauses[:cut_count] + cube`, confirm `sha256(leaf.cnf) == proof.cnf_sha256`, confirm `sha256(leaf.drat) == proof.proof_sha256`, and replay via `drat-trim -L leaf.lrat` + `lrat-check` to produce compact archival LRAT certificates.
3. **Checkpoint Schema v2 Invariants (Zero Progress Loss)**:
   - Atomic `write + fsync + rename` for `checkpoint.json`.
   - Strict append-only byte-prefix invariant on `cuts.jsonl` (verified by `continuation.py`'s `cut_prefix`).
   - Monotone tree invariant: no previously `SPLIT` node may change `split_var`, no `CERTIFIED_UNSAT` leaf may be dropped, and `resume` directory is read-only (must differ from `out`).

---

## 4. Controlled Benchmark Protocol (Pre-Bulk-Launch Gate)

Per `milestone-2026-11-27.md`, **no bulk GitHub Actions run is authorized** until a small controlled benchmark proves material improvement in certified terminal yield:
1. **Benchmark Set A (Proof-First Recovery)**: Run `v8_proof_first_worker` on `D8-N8-B0-P000-T01` (12 `UNSAT_UNCERTIFIED` leaves) + 3 representative hard `OPEN` v7 checkpoints. Measure: certified leaves/hour, wall time to certificate, proof bytes (DRAT vs LRAT), and verification time (`drat-trim` vs `lrat-check`).
2. **Benchmark Set B (D9-C7 4-Core Run)**: Download McKay's `r38_27.g6.gz` (verify count=477,142, extract all 4 85-edge graphs), run `d9c7_compact_cnf.py` with Kissat + `drat-trim -L` + `lrat-check` on all 4 cores in parallel (4 single-core runners). Compare wall time and proof size against Kaggle v4's 3.5-hour 0/4 timeout.
