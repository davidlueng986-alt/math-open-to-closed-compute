# A complete obstruction to the path-consequence closure route

## Exact proposed lemma and its refutation

The tempting global lemma was: a finite graph with at least two vertices, in
which every distinct vertex pair has a simple path of length `2^k`, `k >= 2`,
must contain a simple cycle of such a length. If true, it would combine with
the already verified all-pairs theorem for cubic `MinimalBad` graphs.

The lemma is false. The stronger fourteen-vertex witness below simultaneously
satisfies the available path conclusions from the earlier waves:

- Every pair of distinct vertices has a simple path of length four or eight.
- For vertices that are distinct, nonadjacent and have no common neighbor,
  there are two such paths with distinct first neighbors.
- Every induced two-edge path lies on a nine-cycle and also on a six- or
  ten-cycle. These are respectively `2^3 + 1` and `2^k + 2` for `k = 2 or 3`.
- The graph is triangle-free and all degrees lie between two and three.
- There is no power-length simple cycle.

Thus even the conjunction of these path conditions does not supply the
missing global forcing theorem. A successful implication must use additional
information, such as the full minimum-degree/global-minimality hypotheses,
or stronger compatible path information.

## Explicit graph

Vertices are `0, ..., 13`. The eighteen undirected edges are

```
(0,3), (0,6), (0,11), (1,4), (1,7), (1,10),
(2,4), (2,11), (2,13), (3,7), (3,12), (5,10),
(5,12), (6,9), (6,10), (7,8), (8,13), (9,13)
```

For unambiguous machine-readable pairs use `witness14.json` or the `edgeList`
definition in `AllPairsObstruction.lean`.

There are eight degree-three vertices and six degree-two vertices:
`4, 5, 8, 9, 11, 12`. Therefore the graph is **not Near**, is **not cubic**,
and is **not a counterexample to the original Erdős–Gyárfás conjecture**.
It does not close any of the thirteen remaining terminal classes.

The independent checker enumerates all twenty-nine simple cycles. Their
lengths and multiplicities are:

| Length | Multiplicity |
|---:|---:|
| 6 | 5 |
| 7 | 6 |
| 9 | 4 |
| 10 | 5 |
| 11 | 6 |
| 12 | 1 |
| 14 | 2 |

There are ninety-one unordered vertex pairs, forty-three distant unordered
pairs, and thirty induced two-edge paths. Every one satisfies the appropriate
condition above. Deleting any vertex leaves a connected graph, so the
independent Python check also establishes biconnectivity; the Lean theorem
currently does not include that extra assertion.

## Formal verification scope

`AllPairsObstruction.lean` imports the existing `Shadow.lean`, hence uses the
same original `Erdos64Closure.HasPower` predicate. It constructs actual
`SimpleGraph.Walk` objects and proves their path/cycle conditions. Its final
`E64AllPairsObstruction.counterexample` combines all of the stated path
conditions with triangle-freeness, degree bounds, `¬HasPower G`, and `¬Near G`.

For absence of power cycles, the proof checks lengths four and eight by
ordinary kernel reduction and proves that every simple cycle has length at
most fourteen. Hence all exponents `k >= 4` are excluded mathematically; this
is a full proof for the specified finite graph, not a bounded search being
extrapolated to arbitrary order. There is no `native_decide`, unproved custom
axiom, or intended proof placeholder. GitHub Actions compilation must pass
before the formal result is marked verified.

`verify_witness.py` independently checks the JSON graph, all path witnesses,
all simple cycles and every path-condition quantifier. It runs from any
working directory:

```
python verify_witness.py --output independent-audit.json
```

`make_lean14.py` regenerates the Lean certificate from the exact JSON data.
The smaller ten- and twelve-vertex exploratory witnesses are superseded and
need not be published as separate results.
