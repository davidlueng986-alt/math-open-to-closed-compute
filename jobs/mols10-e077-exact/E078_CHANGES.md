# E078 exact-search repair and validation

Baseline: compute repository `6dd844e077d207dd2e487b5f5d428593a30ee1b1`,
`jobs/mols10-e077-exact`. Queue schema remains `mols-cube-queue-v1`.
`encode.py`, `coverage.json`, `verify_family.py`, `pysat_worker.py`, and
`ENCODING.md` are byte-for-byte unchanged. All six regenerated order-10
CNF hashes match the existing coverage manifest.

## What changes

1. Branch selection applies occurrence-indexed unit propagation and bounded
   failed-literal lookahead. It skips candidates whose positive or negative
   branch is immediately inconsistent under BCP. The default maximum is
   64 candidate probes; reaching that limit permits an untested candidate.
   This is a heuristic for selecting a variable, not a proof rule: no clause
   is added, no saved cube is changed, both binary children are retained,
   and no negative leaf is accepted without certificate verification.
   If both polarities conflict, the leaf remains unresolved for the solver.
2. Default solver slices are 3,600 seconds. Learned clauses remain in the
   running solver for that slice; there is still no learned-clause resume
   across separate solver processes.
3. Proof storage is bounded and configurable. Defaults are 16 GiB requested
   DRAT cap, 8 GiB disk reserve, and expansion factor 3. The effective cap is
   `min(requested, floor(max(0, free - reserve) / factor))`. Solver and
   proof-conversion/checking processes also monitor remaining disk space.
   The factor is a storage allowance, not a theorem bounding LRAT expansion.
4. A completed proof whose checking reaches a time or disk limit is retained
   as `UNSAT_AWAITING_VERIFICATION`. Existing LRAT files with recorded hashes
   are replayed directly during resume, preserving their bytes. A failed
   replay never closes a leaf.
5. CLI SIGTERM unwinds cleanup, terminating the separately grouped solver
   or checker processes before exit. Interrupted state remains resumable.

## Binary DRAT correction

E077 already wrote binary DRAT. The pinned
[Kissat 4.0.4 source](https://github.com/arminbiere/kissat/blob/8af8e56f174b778aef3aa45af9f739b2a5f492c2/src/application.c)
defaults to binary output for a regular proof file; stdout and `--no-binary`
select ASCII. The production command is unchanged and no unsupported
`--binary` option is added. PySAT retains ASCII proofs. There is no claimed
speedup from changing proof format.

## Validation gate

Run `python3 jobs/mols10-e077-exact/test_e078.py --out out/e078-validation`
inside the pinned SAT image. Optional executable paths are `--kissat`,
`--drat-trim`, and `--lrat-check`.

The local gate passed using Kissat
`8af8e56f174b778aef3aa45af9f739b2a5f492c2`, DRAT/LRAT tools
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, and python-sat 1.8.dev24:

- Sixty small CNFs checked against exhaustive truth assignments; a forced
  literal example verifies candidate exclusion without dropping children.
- All six original CNF hashes reproduced exactly; the ten recorded fast
  E077 negative leaves were inspected. Four are detected by BCP lookahead
  and their old split candidates are avoided. The other six require stronger
  reasoning and are not claimed to be eliminated by this heuristic.
- Actual Kissat binary, Kissat ASCII, and PySAT ASCII pigeonhole proofs all
  passed DRAT-to-LRAT conversion and independent LRAT checking.
- Actual small-order Kissat SAT witness and UNSAT certificate queues passed.
- Time and disk deferral preserved completed DRAT; existing verified LRAT
  resumed with a deliberately unusable converter path and unchanged
  CNF/DRAT/LRAT digests, demonstrating direct replay.
- Existing lifecycle tests passed interrupted-leaf recovery, two-child
  coverage, independent certificate replay, duplicate-child rejection, and
  proof-digest mutation rejection.
- The production wrapper's separate two-second timeout integration test
  confirmed checker termination, preserved certificate bytes, and deferred
  verification status.

These are implementation and certificate-pipeline validations. They do not
assert a witness, complete exhaustion of any order-10 shard, or completion
of the overall mathematical task.
