# Erdős 64: closure-critical Lean investigation, 2026-11-27

The exact original problem and all thirteen unresolved terminal classes remain OPEN.
This package develops and checks specific mathematical steps and route obstructions.
Compilation status is determined by actual Actions logs, never by this source file.

## AllPairsObstruction

An explicit twelve-vertex triangle-free subcubic graph has a simple path of length
four or eight between every pair of distinct vertices, but has no power-of-two
simple cycle. Six vertices have degree two, so it is not Near and is not an
Erdős–Gyárfás counterexample. It refutes the proposed implication from all-pairs
dyadic-path existence alone to a dyadic cycle. Full degree and minimality
hypotheses cannot be discarded when applying the existing Wave 2 path theorem.

Lean constructs all sixty-six unordered-pair paths, reverses them for the other
orientations, checks every closed walk of lengths four and eight using Mathlib's
finite walk enumeration, and proves that every simple cycle has length at most
twelve. The bound connects the finite checks to the unbounded HasPower predicate.
The finite proof uses kernel reduction; no external executable's output is trusted.

The independent Python witness file records all fourteen simple cycles and all
sixty-six path witnesses. It is an independent cross-check, not a Lean premise.

## MinimalCutCompletion

For an inclusion-minimal nontrivial matching two-edge-cut side A of an arbitrary
finite cubic graph, add an edge between its two internal boundary vertices.
The proof establishes that this edge did not already exist, every resulting
vertex has degree three, and every nonempty proper cut has at least three edges.
The theorem is uniform in graph order. It does not assume a fixed finite bound
or absence of power cycles, and therefore applies to the relevant MinimalBad
cubic cut classes. A separate bridge converts ordinary inclusion-minimality
among nontrivial two-cut sides into the exact internal SideMinimal predicate.

This formalizes the structural completion step. It does not align the dyadic
exponents on opposite sides, prove the original conjecture, or exclude either
entire cubic two-cut terminal class. No new leaf status is assigned.

## Verification

The workflow uses the existing pinned Lean 4.36.0 / Mathlib mathematical toolbox,
sets each job's timeout to forty-five minutes, treats Lean warnings as errors,
audits the named declarations' transitive axioms, and saves source hashes and logs.
It runs only on changes to this package or by explicit manual dispatch.
