# ERDOS-64 continuation: precise route obstructions

The original conjecture remains OPEN. No additional one of the thirteen residual Closure DAG leaves is discharged in this package. The existing thirteen full Lean exclusions remain exactly as verified at ad7ace7124fcb6fbfb253a731193e5fa89c552a7, run45633640478.

## Substantive findings

- CONNECTED_CUT2_EQUIVALENCE.md proves that the unrestricted connected matching-two-cut version is already equivalent to the original conjecture, using five copies of a hypothetical counterexample joined around C5. A genuinely more focused low2 proof must use global MinimalBad structure.
- TWO_CUT_GAP.md and obstruction.py give one explicit biconnected fifty-vertex power-free graph realizing all elementary scalar surgery requirements while its crossing spectrum misses every dyadic. It has forty-two degree-two vertices: NOT Near and NOT an original counterexample.
- ARBITRARY_GADGET_EXCLUSION.md gives an all-order ordinary proof eliminating every arbitrary cubic completion of copies of the six-vertex four-port gadget. The proof uses Grossman–Häggkvist's established regular-color alternating-cycle theorem. No Lean verification of that external theorem or this full graph construction is claimed.
- audit.py checks exact local spectra and arithmetic transcription, and gives a cubic bipartite eighteen-vertex graph in which no cycle alternating with a specified perfect matching is dyadic, although the graph itself has C8 and C16. Existence of an alternating cycle alone therefore cannot finish a residual class.
- degree_pruning_obstruction.py gives a C4-free thirteen-vertex two-port graph with one internal degree-four vertex but no Near subgraph. It has C8 and is NOT a power-free witness; it blocks a degree-only cubicization shortcut.

## Verification scope

Run the three standard-library Python scripts. They each create a JSON certificate beside the script. These checks verify the specified finite obstructions, explicit cycles and peeling certificates. Bounded arithmetic regression supports the written infinite argument but is not itself a universal proof. No finite absence result or successful workflow is a closure of Erdős64.

The active mathematical fronts are the twelve residual small-cut leaves and the single cubic nonbipartite triangle-free core leaf C-N-R. All exact predicates and statuses are preserved. No additional recurring work or solver sweep is configured.
