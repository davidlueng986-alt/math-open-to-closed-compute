# CAP062: cap-specific sumset lemmas in Lean

This job kernel-checks reusable lemmas for caps in a finite additive group and for the three layers of a cap in `G × ZMod 3`.

## Main theorem

For a cap `K`, let `K₀`, `K₁`, `K₂` be its three layers. For any finite supersets or enlargements `A`, `B` of the first two layers, and `c ∈ K₂`,

```
#{(a,b) ∈ A × B : a+b = -c} ≤ |A \ K₀| + |B \ K₁|.
```

The formal statement does not need subset assumptions: it counts the original endpoints that are absent from each actual cap layer. It follows by charging each representation to a deleted endpoint; addition cancellation makes each endpoint occur at most once for a fixed sum.

The source also proves exact ordered-pair/fiber counting, mixed-sum avoidance for the actual three layers, disjointness of the negative cap and its restricted sumset, and the cardinality bound `|S| + |S restricted-plus S| ≤ |G|`. Nonempty examples attain both bounds.

## Reproduce

Toolchain: Lean 4.36.0. Mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
The workflow pins the already tested container by digest:
`ghcr.io/davidlueng986-alt/math-compute-lean@sha256:8ba27c4e6be1aff22d80e6444f3ef7a4d0fc0438bcadf55ef39d2c17c74ae116`.

Inside that container:

```sh
cd /opt/mathlib4
lake env lean -DwarningAsError=true /path/to/CapSumset.lean
```

Every headline theorem has a `#print axioms` audit. CI accepts only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; it rejects unproved or native-evaluation axioms. The workflow checks exact source bytes and preserves the source, versions, compiler log, and a machine-readable result.

## Scope

The theorems are finite combinatorial lemmas. This is not an end-to-end Lean proof of the seven-dimensional upper bound or of the exact cap-set maximum. No imported classification theorem is assumed in this module. A successful Actions run is required before calling this source verified.

The isolated branch is `capset/cap062-sumset`; the workflow is `.github/workflows/capset-sumset-lean.yml`. This is a finite verification job with a 20-minute hard limit, not a recurring task.
