# v7 continuation — 2026-11-27

The first pilot and rollout finished: 279 task checkpoints comprise 47 tasks whose terminal CNFs were DRAT-certified by the worker and 232 OPEN tasks. No complete nonempty D678 band was closed. Mathematical encoding audit remains pending; the Ramsey root is OPEN.

This user-authorized bounded continuation restores exactly the 232 OPEN tasks. The source manifest records every original task and immutable checkpoint artifact. It retains the 47 completed source certificates instead of recomputing those tasks. Both downloaded source plan hashes and the common profile certificate are verified before selecting the matrix. Independent reconstruction matched the original 247-task rollout and 32-task pilot, covering all 48 D678 bands (44 nonempty and four empty).

Before releasing the matrix, a real interrupted checkpoint (D6-N9-B3-P000-T01, 31 nodes and 16 OPEN leaves) is restored with no new solving. Task and base identities, all saved nodes and attempts, and the complete cut-stream prefix must survive unchanged. Earlier certified-only resume gates remain recorded in run 45715254768.

Every worker requires its original checkpoint and validates source counts, task identity and tree coverage. Missing downloads fail; they cannot silently restart an empty search. The worker reconstructs the exact base CNF and reruns DRAT on every restored certificate. Witness checkpoints are protected from ordinary continuation, and the source directory cannot be overwritten by its output.

The workflow runs at most 15 workers simultaneously. Each worker has a 3,000-second search/verification budget, 180-second cube slices and maximum depth 7. Proof generation/replay is ordinarily bounded by 240 seconds, increased to 900 seconds for D8-N8-B0-P000-T01, whose 12 uncertified UNSAT terminals are the priority. The 90-minute job timeout allows setup, restore and artifact upload. This is one finite batch, with no schedule or recursive dispatch.

Each worker saves checkpoint-<task> plus a compact result-<task>. The final reconcile job downloads the compact results and accounts for all 279 original tasks in v7-progress-summary (progress.json and summary.md). OPEN is a mathematical search outcome, not a failed execution. Missing or invalid evidence produces an incomplete report and failed reconciliation. New witnesses require the independent original-graph verifier and remain visibly flagged for final review.

All artifacts use 90-day retention. Original completed artifacts are retained in their source runs. D9 uses its separate Kaggle encoder and is outside this D678 continuation.

## Source runs

- Pilot: https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45713450151
- Rollout: https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45715254768

The continuation workflow is `.github/workflows/ramsey-r310-cubes-v7-continue.yml`. Its launch marker and source manifest specify this exact wave; later continuation must use the newer checkpoint evidence rather than rerunning the old source manifest.
