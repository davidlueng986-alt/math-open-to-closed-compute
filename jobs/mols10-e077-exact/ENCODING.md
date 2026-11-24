# E077: exact original-space search with persistent cubes and proof checking

Task status at implementation handoff: **未完成任務**. No order-ten witness or
completed order-ten exhaustion is claimed by this package. It supplies an
exhaustive domain reduction, a compact equivalent Boolean formulation, and
a resumable certificate-producing search. Long searches are finite jobs;
their unresolved cubes survive interruptions and time limits explicitly.

## 1. Global domain reduction: six cycle shards, 31 first-pair representatives

Write each row of each Latin square as a permutation of the n symbols. An
m-tuple of Latin squares gives each row an m-bit vector of permutation signs.
When n>2^m, two distinct rows have the same vector. Choose these as rows 0,1.
Independently relabel each square's symbols to make row 0 the identity.
Each new row-1 permutation has sign equal to the product of the old row-0
and row-1 signs, hence is even. These operations preserve all orthogonalities.

For n=10,m=3, the inequality 10>8 applies. In the first square, conjugate the
second-row permutation to a canonical derangement cycle representative p
with p(0)=1. Simultaneously applying the same column and symbol permutation
to all squares preserves the identity first rows, and conjugates all three
second-row permutations, preserving their even signs. Ordering the rows by
the first square's column-0 values creates an identity first column and keeps
the chosen rows 0,1 in place.

Thus all three second-row permutations may be assumed even. A permutation
of order 10 with c cycles has sign (-1)^(10-c). The six necessary canonical
cycle types are therefore:

| Original 12-shard index | Cycle partition | First-pair representatives |
| ---: | --- | ---: |
| 1 | 2+2+2+4 | 5 |
| 2 | 2+2+3+3 | 4 |
| 6 | 2+8 | 4 |
| 8 | 3+7 | 4 |
| 9 | 4+6 | 6 |
| 10 | 5+5 | 8 |

The odd cycle shards are **not asserted to be individually impossible**.
Every possible original triple has an equivalent representative among the
six listed shards. That suffices for a global exhaustion.

For the further pair reduction, let sigma commute with p and fix 0. It also
fixes 1=p(0). The transformation

    L'_s(r,c) = sigma(L_s(sigma^{-1}(r),sigma^{-1}(c)))

preserves every normalization, including p and all second-row signs. It
maps the pair {L1(1,0),L2(1,0)} by sigma. Swapping the last two squares sorts
the pair. The centralizer fixing 0 acts by independent rotations and
permutations of equal-length cycles outside the cycle containing 0; that
anchor cycle is fixed pointwise. Explicit orbit enumeration leaves 31 pair
representatives across the six shards. The code independently reproduces
the parent investigation's orbit sets using all equal-cycle swaps.

`coverage.json` records the six precise CNF hashes and all 31 pairs. No
affine, cyclic, layer, relation, or automorphism hypothesis is imposed on the
unknown squares. These are symmetry choices, not structural restrictions.

## 2. Compact composition encoding and its equivalence

For each original square L_s use one-hot variables X_s(r,c,u), meaning
L_s(r,c)=u. Every cell, every row-symbol pair and every column-symbol pair
is constrained exactly once. Fixed normalization entries are constants.
Values already forbidden by those entries are removed from a cell's domain.

For each unordered pair a<b, introduce a further Latin square Z_ab with

    Z_ab(r,u) = L_b(r,c), where c is the unique column with L_a(r,c)=u.

Enforce Z_ab to be Latin, and add the ternary composition clauses

    X_a(r,c,u) AND X_b(r,c,v) => Z_ab(r,u,v).

This uses three original squares and three auxiliary squares for a triple.
It avoids the much larger formulation comparing every pair of cells.

### Forward direction

Given a true MOLS tuple, define each Z_ab by the displayed rule. Its row r
is a permutation because both original rows are permutations. If column u
of Z_ab repeated v in two rows, the original pair (u,v) would occur twice,
contradicting orthogonality. Thus Z_ab is Latin. The composition clauses all
hold. The normalized first rows force Z_ab(0,u)=u, as imposed by the code.

### Reverse direction

Take a satisfying assignment. The original cell/row/column constraints give
Latin squares. If original squares a,b repeated ordered pair (u,v), their
cells cannot be in the same row, because the first square's row contains u
only once. In two distinct rows r,r', the composition clauses force
Z_ab(r,u)=Z_ab(r',u)=v, contradicting its column Latin condition. Therefore
the original squares are orthogonal.

### Normalized diagonal exclusion

Outside row 0, no original L_s(r,c) can equal c, by the column Latin
condition. Two original squares cannot both have value u at a cell outside
row 0, because their (u,u) pair already appears at (0,u). In the composition
encoding this is also forced by Z_ab's identity first row and column Latin
condition. Domain pruning and simplified composition clauses incorporate
these consequences without a separate restricted model.

The composition formulation follows the same general approach described in
Aaron Barnoff and Curtis Bright, *Improving SAT Solvers on Orthogonal Latin
Square Problems*, arXiv:2605.02132v1, Section 3.1. The proof above specifies
the exact orientation used by this implementation:
https://arxiv.org/html/2605.02132v1 . No novelty claim is made for the encoding.

## 3. The even-permutation cuts are actually in the CNF

For each of L1,L2's second rows and each pair of columns c<d, an auxiliary
variable records whether the row values satisfy L_s(1,c)>L_s(1,d). For each
possible pair of distinct values u,v, the two selected one-hot variables
force the inversion variable to exactly that comparison. An exact XOR chain
forces the total inversion count to be even. The first square's canonical
permutation is checked even directly.

These cuts add 178 variables and about 6,924 clauses. Each production shard
has **4,748 variables and 79,009--79,013 clauses**. The flag is guarded by
n>2^m; it is not silently applied to order-4 or order-5 controls, where that
global pigeonhole argument is unavailable for three squares.

The inversion gadget was exhaustively checked against direct inversion
parity on all 872 permutations of orders 2 through 6. A genuine triple over
GF(9), represented by F3[i]/(i^2+1), additionally satisfies the full flagged
encoding: L_t(r,c)=t*r+c for t=1,2,i. Its canonical first-square second row
has cycle type 3+3+3. This tests the simultaneous three-square parity cuts
in a domain where the global pigeonhole hypothesis is valid.

## 4. Persistent exhaustive cube queue

Each state directory contains an immutable `base.cnf`, its mapping and hash,
and an atomic `queue.json`. The initial cube is empty. Every split is

    parent cube C => child C AND x, or child C AND NOT x.

Both children are retained. Thus the queue is an explicit finite binary
coverage tree over the entire shard formula. `verify` checks that every
child is exactly its parent plus the indicated literal or its negation,
that no child is omitted or repeated, and that all nodes are reachable.
Split selection uses original square variables first and avoids variables
already fixed by simple unit propagation. This heuristic never closes a
branch or introduces a learned clause.

The worker handles outcomes as follows:

* SAT: independently check every CNF clause, decode the original squares,
  and directly verify every row, column and orthogonal pair. Only then mark
  the leaf `SAT_VERIFIED`.
* UNSAT: preserve the exact CNF including cube unit clauses. Check the DRAT
  proof with `drat-trim -L` and independently check the resulting LRAT with
  `lrat-check`. Only both successful checks permit `UNSAT_VERIFIED`.
* UNKNOWN: retain the unresolved cube, normally replace it by its two
  explicit child cubes, record solver statistics and the incomplete proof's
  size/hash, and discard that incomplete proof. No branch is certified away.
* Checker limit/failure: retain `UNSAT_UNVERIFIED` or
  `UNSAT_AWAITING_VERIFICATION`, its full proof, and its cube for retry.
* Job interruption: a persisted RUNNING leaf is requeued. A completed SAT
  model or UNSAT proof found in the old attempt is recovered and checked.
  Unfinished proofs are recorded and removed; the cube itself is never lost.

One writer holds a filesystem lock per state directory. Atomic replacement
prevents a partial queue file from becoming the latest checkpoint. A queued
cube resumes with a fresh solver invocation; this is a persistent search
partition, **not a serialization of the solver's entire internal learned
clause database**.

## 5. Verification boundary

`verify` regenerates the base formula from its recorded parameters, checks
its exact hash, verifies the full coverage tree, reconstructs every completed
leaf as base clauses plus cube units, and replays each LRAT proof. It does
not trust a cached closure flag. `verify_family.py` additionally checks that
all six required shards are present and have the exact manifest hashes
before accepting a full-family UNSAT result. A single directly verified
order-ten triple would suffice for the constructive answer.

The mathematical normalization and encoding equivalence are proved above.
The Python encoder, queue checker, and C proof checkers are not themselves
formalized in Lean here. The independent LRAT checker reduces dependence
on the SAT solver and on DRAT proof reconstruction; it does not formally
verify the entire original-problem-to-CNF reduction.

## 6. Meaningful completed controls

The saved `validation/summary.json` records:

* Correct SAT witnesses for a Latin square of order 2, two MOLS of order 3,
  three MOLS of order 4 with cycle type 2+2, and three MOLS of order 5.
* DRAT and independently checked LRAT proofs for two MOLS of order 2,
  three MOLS of order 3, and the order-4 triple shard with a 4-cycle.
* Complete enumeration of the normalized order-4, cycle-2+2 original-square
  projections: exactly one triple after the stated symmetries. Its blocking
  formula is UNSAT with both proof checks. Auxiliary-variable assignments
  are not counted as distinct original tuples.
* All 872 parity-gadget checks and the full GF(9) flagged positive control.

`test_queue.py` exercises SAT completion, two-branch UNSAT completion,
interrupted-state recovery, and rejection of a duplicated child or altered
proof digest. These are tests of concrete certificate and coverage risks,
not brief probes of the order-ten search.

## 7. Long-job interface

The six required indices are 1,2,6,8,9,10. For each index I:

    python3 queue_search.py init --state STATE --n 10 --squares 3 --shard I --even-row-normalization
    python3 queue_search.py run --state STATE --seconds 18000 --slice-seconds 900 --check-seconds 900
    python3 queue_search.py verify --state STATE --lrat-check lrat-check

`run` defaults to external `kissat`, `drat-trim`, and `lrat-check`. The
existing compute image provides the pinned tools. A 900-second solve slice
gives CDCL learning time to develop; its timeout produces a persistent split,
not a spurious rejection. The 18,000-second overall budget reserves time for
both proof checks and cleanup. The outer job should allow at least another
20 minutes for verification and durable artifact upload, still below six
hours. Final replay time depends on the completed certificate sizes; if a
job cannot finish replay, retain its files and replay on continuation.

The default proof-size cap is 2 GiB per solver attempt. Completed proofs
are retained and may require substantial artifact space. Incomplete proof
files do not accumulate. No automatic recurring run is installed.

Resuming uses the same complete state directory and the same `run` command.
It must not replace `queue.json` with a newly initialized empty state. To
combine retrieved states, create a JSON mapping such as
`{"1":"/path/shard1","2":"/path/shard2",...}` and run:

    python3 verify_family.py --manifest coverage.json --states states.json --out family_verification.json

Missing states and unresolved cubes remain visible with task status
**未完成任務**. Solver branch counts and resolved-cube counts are never turned
into a percentage of the mathematical problem solved.
