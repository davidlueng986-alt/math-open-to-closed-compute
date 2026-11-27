# Erdős 64: closure-critical Lean investigation, 2026-11-27

The original problem and all thirteen remaining terminal classes remain OPEN.
Actual successful Actions logs determine verification status.

## Cubic minimal two-cut completion

`CutCompletionApplication.lean` starts with exactly `MinimalBad G`, `Cubic G`,
and `SmallCut G 2`. It selects an inclusion-minimal nontrivial cut side,
proves the boundary is a matching of size two, and adds the previously absent
edge between its inside ports. The resulting strictly smaller simple cubic
graph has every nonempty proper edge cut of size at least three and contains
a power-of-two cycle; the original induced side contains none. This is uniform
in graph order. `MinimalCutCompletion.lean` supplies the structural proof.
See `CUT_PROOF.md` for the full argument and remaining port-length coupling gap.
This does not exclude either entire cubic two-cut terminal class.

## Path-consequence obstruction

`AllPairsObstruction.lean` constructs a fourteen-vertex triangle-free subcubic
graph with all-pairs dyadic paths, two distinct dyadic-path exits for every
distant pair, and both Fermat and dyadic-plus-two cycles through every induced
P3. Nevertheless it has no power-of-two cycle. Six vertices have degree two,
so it is not Near and is not an original counterexample. The full minimum-degree
and global-minimality information cannot be discarded. See `PATH_OBSTRUCTION.md`.

All finite certificates are actual SimpleGraph.Walk proofs checked by ordinary
kernel reduction. Lengths four and eight are checked, and the simple-cycle
order bound excludes every larger power. `verify_witness.py` independently
checks `witness14.json`; its output is not a Lean premise. `make_lean14.py`
regenerates the certificate. Earlier exploratory witnesses are superseded.

## Verification

The workflow reuses the existing Lean 4.36.0 / pinned Mathlib GHCR toolbox,
limits each job to forty-five minutes, treats warnings as errors, rejects
proof placeholders/custom axioms/native_decide, prints transitive axiom lists,
and records source hashes, toolchain and actual logs. Only standard Lean
axioms (propext, Classical.choice, Quot.sound) are allowed. No new leaf status
follows merely from this package compiling.
