# E077: constructive search with Latin trades and exact common transversals

This job searches for three mutually orthogonal Latin squares of order10. It starts from validated orthogonal pairs, changes their actual combinatorial structure, and tests extension by the Euler–Parker method. It is a heuristic generator around exact inner searches. A successful witness closes the existence question; failure or a time limit does not prove global nonexistence.

## Run

The executable uses only the C++17 standard library. Verification uses only the Python standard library.

```
bash run.sh 770101 19000 out-770101
```

Use independent seeds770101,770102,770103,770104 for four jobs. Each call above gives the search19000 seconds (5h16m40s), with a checkpoint every30 seconds. A350-minute workflow timeout leaves a margin for compilation and verification. Upload the entire output directory even on timeout.

The full CLI is:

```
g++ -O3 -std=c++17 -Wall -Wextra -Wpedantic search.cpp -o search
./search --input seeds.txt --out out-770101 --seed 770101 --seconds 19000 \
  --mate-nodes 200000 --pack-nodes 200000 --mates 16
python3 verify.py out-770101/checkpoint.json --exhaustive --report out-770101/verified.json
```

Resume a saved population and PRNG state with the same search parameters:

```
./search --input seeds.txt --out out-770101 --seed 770101 --seconds 19000 \
  --mate-nodes 200000 --pack-nodes 200000 --mates 16 \
  --resume out-770101/resume.txt
```

The wrapper automatically resumes when its output directory already contains `resume.txt`. The resume file preserves the top32 pairs and PRNG state; it does not preserve the complete deduplication cache or the in-flight annealing state. Therefore this is a restart from a saved population, not a promise of a bit-identical uninterrupted trajectory. No recurring job is configured.

## Algorithm

Every candidate is an exact orthogonal pair(A,B), so both squares are always Latin and their overlay has100 distinct ordered pairs.

1. Enumerate all common transversals of A and B by an exact row/column/symbol backtrack using minimum remaining values.
2. Search for a maximum family of pairwise disjoint common transversals. A family of10 gives the third Latin square immediately. The search saves a concrete packing, not just a numerical score.
3. Mutate the pair either by a pair-preserving two-level component switch, or by a Latin trade in one square followed by exact-cover reconstruction of mates of that new square.
4. During most mate reconstructions, retain common transversals from the parent that remain valid in the changed square. A proposed mate transversal is allowed only when it intersects each retained transversal at most once. This forces the reconstructed pair to retain those partial third-square classes.
5. Use a population of up to128 candidates and a changing acceptance temperature. Coordinate permutations of the four-column OA change which Latin trades are explored. Alternate broad restarts with mutations near the best packings.

The fitness compares the disjoint packing size first and total common-transversal count second. The initial Wanless near-pair has exactly14 common transversals, with maximum disjoint packing7. Increasing the count alone is not a solution. Obtaining a full packing of10 is the success condition.

`--mate-nodes` caps the reconstruction search for each mutated Latin square and `--mates` caps the number of mates emitted. These limits deliberately restrict candidate generation. `--pack-nodes` caps maximum-packing analysis; if reached, the saved `packing_search_complete` is false and the saved packing is only a certified lower bound. None of these limits licenses a nonexistence claim.

The deduplication key uses a limited normalization of rows and symbols. Distinct saved keys are labelled normalized pairs, **not certified distinct isomorphism or paratopy classes**. Counters named `evaluated_pairs` count actual evaluations and can include reevaluations of parent pairs; `valid_mutants` counts new normalized pair keys accepted for evaluation in the current session. No novelty claim is made for any discovered pair.

## Exact reduction lemmas used by the code

### Common-transversal completion

An orthogonal pair(A,B) extends to three MOLS exactly when its100 cells partition into ten common transversals. The classes of symbols in the third square give the partition; assigning distinct symbols to the transversals gives the converse. This is the standard Euler–Parker principle applied to a pair.

### The last transversal is forced

If n−1 disjoint common transversals are chosen, every row, column, A-symbol and B-symbol has exactly one remaining cell. Their complement is the final common transversal. Thus a maximum packing cannot equal n−1.

### Two remaining transversals reduce to bipartiteness

After n−2 disjoint common transversals, each of the four coordinate values occurs exactly twice among the remaining2n cells. Join two residual cells whenever they agree in any coordinate. Two remaining common transversals exist exactly when this graph is bipartite.

A two-colouring puts the two occurrences of each coordinate on opposite sides, producing the transversals. Conversely, the two transversal classes give such a colouring. If the graph is not bipartite, an odd cycle is an explicit obstruction to extending that chosen partial packing. Together with the previous lemma, this also excludes a packing of n−1 extending that partial choice.

The C++ search uses this lemma as soon as it reaches n−2 classes. It replaces deeper branching with BFS and can save `two_remaining_odd_cycle`. The independent verifier checks that the listed cycle is odd, simple, residual and made of valid coordinate-sharing edges. Such a certificate concerns the specified partial packing only.

### Pair-preserving component switches

Represent a pair by the100 OA rows(r,c,A[r,c],B[r,c]). Select two values in one coordinate. Each of the other three coordinates pairs the20 selected rows by equal value. Swapping the selected coordinate's two values throughout one connected component preserves every two-coordinate projection: for each other coordinate, both occurrences in its matched pair are swapped together. This gives another exact orthogonal pair.

A standard two-symbol cycle swap in an individual Latin square similarly preserves every row and column. The changed square's mates are then reconstructed from disjoint transversals; no assumption that the old mate survives is made.

## Independent verification and controls

`verify.py` independently checks:

- each saved square has the correct symbols once per row and column;
- the pair has all n² overlay pairs exactly once;
- every saved common transversal has one cell of each row, column and symbol in both squares;
- the saved transversals are pairwise disjoint;
- a reported YES has a full third Latin square, orthogonal to both others;
- optional residual odd-cycle certificates;
- with `--exhaustive`, recomputation of all common transversals and maximum disjoint packing for the best pair.

The wrapper runs two controls before substantive work:

```
./search --self-test positive_control.json
python3 verify.py positive_control.json --exhaustive
./search --input seeds.txt --audit baseline_audit.json
python3 verify.py baseline_audit.json --exhaustive
```

The positive control reconstructs a full3MOLS(5) witness through the same C++ transversal/packing code. The independent check finds10 common transversals and a disjoint packing of5. The negative control exhaustively audits the supplied Wanless pair:14 total transversals, maximum packing7, hence no extension of **that fixed pair**. The status is `RESTRICTED_UNSAT`, with scope recorded explicitly.

On a completed bounded search without a construction, the checkpoint status is `UNFINISHED_TASK` and `status_display` is `未完成任務`; during work the status is `SEARCHING`. A verified construction uses `YES_WITNESS`. The checkpoint never asserts global nonexistence. `iterations` continues across population resumes; the other counters and elapsed time refer to the current process. The wrapper always verifies the saved witness/packing independently. A separate exhaustive final audit is capped at180 seconds; a timeout there does not invalidate a witness that passes the direct checks.

## Seeds and primary sources

`seeds.txt` contains134 validated pairs: the two orthogonal pairs in Wanless's near-triple,32 parity examples and the first100 pairs from his random-pair data file. These are starting data, not results newly discovered here. `source_manifest.json` records source URLs and SHA-256 hashes. `prepare_seeds.py` can rebuild the input after downloading the named public source files.

- Judy Egan and Ian M. Wanless, *Enumeration of MOLS of small order*, Mathematics of Computation85(2016),799–824. Data page: https://users.monash.edu.au/~iwanless/data/MOLS/ . The source page describes the near-example as a pair sharing seven common transversals; the explicit file includes a third square giving overlay counts100,100,91.
- Aaron Barnoff and Curtis Bright, *Improving SAT Solvers on Orthogonal Latin Square Problems*, arXiv:2605.02132v1,2026. https://arxiv.org/html/2605.02132v1 . This primary paper explains why directly invoking Euler–Parker can outperform a declarative SAT encoding, and implements a hybrid method for restricted orthogonal-pair problems. It does not solve3MOLS(10), and its runtime results do not predict the success of this new search. Original source: https://github.com/aaronbarnoff/MOLS_EP . No code from that repository is copied here.
- Curtis Bright, Amadou Keita and Brett Stevens, *Myrvold's Results on Orthogonal Triples of10×10 Latin Squares: A SAT Investigation*, Electronic Journal of Combinatorics33(1),P1.30,2026, DOI10.37236/13960. The eight constructed pair types concern a restricted4×4-subsquare framework; satisfying a pair type does not supply the third square. https://www.combinatorics.org/ojs/index.php/eljc/article/view/v33i1p30 .

The downloaded public corpus and selected input contain mathematical arrays only. No user-private data is sent to external services by this job.
