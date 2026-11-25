# P vs NP desk step L-meta-3241

For a nonempty graph G, the cheapest star list in the posted Lean statement has cost `|E| + τ(G) - 1`. Every such list has at least `|E|` leaves counted with multiplicity and at least `τ(G)` entries because the centers form a vertex cover. A minimum cover attains the bound by assigning each edge to one of its endpoints in the cover. Every center of a minimum cover owns an edge to a vertex outside the cover, so the construction uses every center. The empty graph uses the empty list.

The search builds exact SAT instances for smaller fan-in-two monotone circuits. The target is tested on its minimal true inputs (the edges) and maximal false inputs (the maximal independent sets). These inputs suffice by monotonicity. Each SAT witness is re-evaluated on every input word. Conflict-budget exhaustion leaves the case unresolved.

Graph representatives are canonical under independent permutations of the two shores. Isolated inputs can be deleted: replacing them in a proposed circuit by any remaining input preserves the function on the remaining inputs. For a graph with `n` non-isolated vertices, a fan-in-two output cone needs at least `n - 1` gates just to read all of them. For the SAT cases, unused gates can be removed, and a shorter circuit can be padded with idempotent copies of its output. Among gates available in topological order, the encoding orders them by larger operand wire, smaller operand wire, and then operation. Minimum circuits cannot have comparable operands on the tested inputs, because the gate could then be replaced by one operand while preserving every tested output. The harness checks that it finds the excluded `K₂,₂` positive control.

```sh
python -m pip install python-sat==1.9.dev25
python jobs/pequalnp-c4-search/search.py 4 4 --output result.json
```

A proof route for the already restricted single-AND-level case is to read each AND gate as a star. Its two OR supports are disjoint, and their cross product is contained in the graph. No four-cycle forces one support to be a singleton. An OR gate with at least two distinct leaves cannot serve two different star centers, since two common neighbors would form a four-cycle. For a center with `d` distinct leaves and `k` AND gates, its OR subnetwork needs at least `d-k` gates. The top OR network needs at least `K-1` gates for the `K` AND outputs, giving the required bound. The upstream `L-meta-2656` proves a related result under the stronger condition on the circuit than in the desk statement, that each AND separately implies the output function. The unresolved part is charging gates shared among mixed OR blocks in the unrestricted circuit.

These calculations are finite evidence. The desk statement requires a general Lean proof or an explicit counterexample.
