# CAP066 — exact replay of 236 ≤ r₃(7) ≤ 279

This standalone bundle verifies an existing 236-point cap in F₃⁷ and a
computer-assisted exclusion of every 280-point cap. A larger cap would contain
a 280-point subset. The exact value of r₃(7) remains open.

The upper-bound argument uses published classification theorems, explicitly
listed below. The bundle replays all new finite certificates and all finite
structural reductions needed for this bound. It does not redo the original
five- and six-dimensional classifications, and it is not an end-to-end Lean
formalization. Floating-point discovery output is never an acceptance condition.

## One command

Use Python 3.10 or later and GCC with C++17 and signed `__int128` support:

```bash
python3 run_verify.py --workers 2
```

The script works from any current directory. It uses only the Python standard
library and the C++ compiler; it needs no network, solver, downloaded packages,
or other research folders. It compiles its eight C++ checkers in a temporary
directory, verifies SHA-256 hashes, regenerates all admissible grids, checks
all integer separators, and writes `VERIFICATION_RESULT.json` beside the script.
An optional `--output path/to/result.json` changes that destination. Do not run
Python with `-O`: assertions are proof acceptance conditions. The compiler
command deliberately retains C++ assertions.

Expected final result:

```text
status: PASS
lower_bound: 236
upper_bound: 279
branches: 242
raw_grids: 1974032142
admissible_grids: 273592522
```

The grid counts include repetitions across certificate branches. They count
labelled integer count grids, not distinct caps. Runtime depends on the CPU;
two workers are the maximum accepted by this runner. All arithmetic relevant
to acceptance is integral. Checked 128-bit operations are used in the structural
checkers, and the wrapper bounds every dot product in the generic checkers
strictly below the signed 128-bit range.

## Proof and dependency order

Read `PROOF.md` for the global argument. The runner checks all branches in this
acyclic order:

| Stage | Branches | Result used later |
|---|---:|---|
| Two slices of size at least 110 | 7 | Every parallel triple has median at most 109 |
| A largest slice of size 110–112 | 101 | Every six-dimensional slice has size at most 109 |
| A 109-point slice completed to Hill112 | 96 | No 109-point slice completes to Hill112 |
| P0 = (109,109,62) | 1 | P0 is excluded |
| Completed108 in four contexts; completed107 in one context | 20 | Completion cuts are active only in the proved contexts |
| P1 = (109,108,63), six centroid-rank cases | 6 | P1 is excluded |
| P2, P3; P4 in six centroid-rank cases | 8 | P2, P3, P4 are excluded |
| P5, P6, P7 | 3 | The final three profiles are excluded |
| **Total** | **242** | All negative profiles of the global polynomial are excluded |

The final polynomial is

\[
425911502-25071(a^2+b^2+c^2)+94(a^3+b^3+c^3).
\]

The standard-library checker checks all 208 possible sorted profiles with
sum 280 and maximum 109. It is nonnegative except on the eight separately
excluded profiles, yet its forced sum over all 1,093 projective directions
is **−1,508,274**. This supplies the final contradiction.

The 20 local completion branches comprise all four deletion cases for an
A=108 slice with B=106,107,108,109, and all four cases for A=B=107. None is
promoted to a ban on completed108 or completed107 slices in other contexts.
The four cases are indexed by deleted antipodal-pair count and whether the
anchor point sum is zero; they are not claimed to be affine orbit classes.

## Finite geometric inputs replayed here

`checks/verify_foundations.py` starts from the point lists. It checks all
27,730 unordered pairs of the 236-point cap, all 6,216 pairs of Hill112,
the Hill convolution on all 729 vectors, the full negative Fourier support,
all 112 one-point deletions and all 6,216 two-point deletions, and the exact
point/pair incidences used in Hill-minus-four/five moments.

The remaining auxiliary checks are:

- The four Hill-minus-three labelled histograms, independently reconstructed
  by exact character projection (`docs/HILL_MINUS3_CLASSIFICATION.md`).
- The five-hole lemma: all 10,890 conflict graphs and all 609,840 six-subsets
  (`docs/FIVE_HOLE_COMPLETION.md`).
- Translation/reflection convolution of the 45-cap, the 22-hole cap, and its
  112-point completion.
- The (43,43,h≥22) completion theorem: all 52,488 completed pairs in the
  two forced cross-section orientations, reconstructed from affine frames
  (`docs/CROSS_SECTION_COMPLETION.md`).
- Residual centroid rank: the complete six-case linear-algebra split
  (`docs/CENTROID_RANK_REFINEMENT.md`), followed by exact grid replay.

The upper279 proof uses seven explicit double-high certificates and does not
need the inherited deleted-Hill capacity lemma used in the intermediate
upper280 checkpoint. It also does not need the separate stronger four-hole
LP theorem or any unfinished search for a still smaller bound.

## Published classification imports

| Source | Imported role |
|---|---|
| Edel, Ferret, Landjev, Storme (2002), DOI [10.1006/jcta.2002.3261](https://doi.org/10.1006/jcta.2002.3261) | r₃(5)=45 and affine uniqueness of the 45-cap |
| Potechin (2008), DOI [10.1007/s10623-007-9132-z](https://doi.org/10.1007/s10623-007-9132-z) | r₃(6)=112 and affine uniqueness of Hill112 |
| Thackeray (2022), [arXiv:2206.09804](https://arxiv.org/abs/2206.09804), Theorem 2.1 and Theorem 3.9 | Completion of five-dimensional 43/44 caps; 42-cap alternatives; completion of six-dimensional 110 caps |
| Same paper, Proposition 3.5 and its proof, Propositions 3.7–3.8 | Relative 45-cap sumset cases and old sufficient completion criteria |
| Same paper, Lemmas 2.2, 2.3, 3.2, Table 1 and the Delta686 facts in Proposition 3.8's proof | Common 882A2 section direction, direction transitivity, uniqueness under two-point replacement, and the exceptional42 exclusion in the cross-section argument |

The detailed geometric scope and uses of these imports are stated in the
three completion/histogram documents. A 111-cap completes to 112 by applying
the 110-cap theorem to a subset and the verified Hill secant counts: two
missing endpoints cannot permit a new point outside that completion.

## Provenance and integrity

`PROVENANCE.json` maps the copied files to their archived research locations;
these strings are provenance labels, not runtime paths. Inherited research
is pinned to GitHub commit `70312fce018c64d5fe5812bde88df4ebf3046ba7` and archive
SHA-256 `bc40294cb12e61e8d86d174756fb584bb5101b77dddc218b507deb06d4b67ca5`.
All certificate JSON files and C++ checkers were copied without changing their
bytes. The three M280 structural checkers were independently adapted from
the inherited M281 checkers by changing the total and required third-slice
range. The other five C++ checkers are independently written CAP066 checks.

`SHA256SUMS.json` pins this bundle's proof inputs, certificates, checkers,
runner, and documentation. Verification outputs and temporary compiled binaries
are not inputs. Optimizer statuses, discovery timings and discovery-source
hashes retained inside certificate JSON are provenance only; acceptance comes
from the exhaustive integer checker and exact target calculation.
