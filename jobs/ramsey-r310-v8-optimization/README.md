# Ramsey R(3,10) — V8 algorithm optimization (paused; no launch)

The exact v7 task decomposition remains the reference. This directory contains an offline, integer-only filter, not a change to a certified CNF or a new Actions trigger. Conditional on the established cover and MIN6 deduction; mathematical audit remains required.

## New necessary constraints

For adjacent roots 0,1 of degrees d,q let X=N(0) minus {1}, Y=N(1) minus {0}, T the common antineighborhood; let nx=d-1, ny=q-1, nt=40-d-q. X and Y are independent. Write sx,sy for the sums of full degrees in X,Y, t=e(X,Y). Then xt=e(X,T)=sx-nx-t and yt=e(Y,T)=sy-ny-t. All T vertices have at least one neighbor in each of X,Y, by maximal triangle-freeness and the two root nonedges. For a T vertex of degree k, its X and Y neighbor counts are at most min(nx,k+d-11) and min(ny,k+q-11), using the existing nonedge codegree bound. Enumerate the exact compatible degree histograms of X,Y,T with the old v6 type filters, then apply these lower/upper cross capacities.

For x,x' in X, the pair is nonadjacent and shares root 0. Summing codegree(x,x') <= deg(x)+deg(x')-11 over unordered pairs of X gives

    sum_{v in T} C(deg_X(v),2) + sum_{v in Y} C(deg_X(v),2)
      <= (nx-1)*sx - 12*C(nx,2).

Use the exact integer minimum B(s,n) of sum C(a_i,2) for n nonnegative integers with sum s: if s=n*u+r then B=(n-r)*C(u,2)+r*C(u+1,2), by exchanging one unit between two entries differing by at least two. Consequently B(xt,nt)+B(t,ny) <= (nx-1)*sx-12*C(nx,2). The Y analogue is B(yt,nt)+B(t,nx) <= (ny-1)*sy-12*C(ny,2). No graph can be excluded merely by a heuristic. All calculations use integers and the previous necessary conditions. These new inequalities are redundant with the full pair constraints logically, but avoid asking CDCL to discover their aggregate implications.

## Actual local experiment (2026-11-27)

Input: complete v7 plan artifact [15170482260](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45936075262/artifacts/15170482260), ZIP SHA256 bdb5fd354c63887c6e1bcba7a97b684b973c05599e0bb8a13e11b52dfc54f95e.

Run: python group_filter.py --plan plan.zip --out group_filter_results.json

Selftests exhaust all integer compositions for small totals and all 512 labeled 3x3 bipartite graphs for the common-neighbor identity. Passed locally. All 279 task keys verified. Compared with the exact v6-compatible group interval baseline, 99,862 feasible (task, profile, exact cross-edge count) triples become 79,026 (20,836 removed, 20.86%). 177 tasks have reduced tables; 8 become empty, all already CNF-certified. Among the 231 unresolved tasks, 96,795 become 77,563 (19.87% fewer). No new task is certified or closed. Output SHA256 cc581deb605ca358b9d9b136d03b07f4971c84f2ac9e54b42e7b6641cb36379e. This is not a speedup measurement, nor a fraction of graph search space or proof difficulty. Independent mathematical audit and SAT integration remain pending.

## Next algorithm work (not yet benchmarked)

1. Integrate allowed (profile,t) tables as exact disjunctive constraints; retain legacy tasks and use separate encoding hashes. For each exclusion emit independently replayable table evidence. Do not change or invalidate existing checkpoint CNFs.
2. Proof-first path on static zero-model cubes: run proof-producing Kissat (or CaDiCaL with certified proof output) directly on a frozen CNF with cube unit clauses, then replay the certificate. Avoid current CaDiCaL search followed by a second search from scratch. SAT relaxation models still require independent graph validation and valid I10 separation. Do not assume incremental proof concatenation is sound.
3. Replace repeated depth-7, 180-second retries with measured conflict/propagation-aware branching on structural degree and cross-edge invariants. Preserve both complementary cases; retain parent coverage. Compare conflict counts, solver and proof-check seconds, and certified terminal yield on identical hard checkpoints.
4. Try exact X-Y skeleton gluing, especially small sparse cross cases; fix each orbit representative and enumerate compatible attachment masks on T. Do not combine incompatible symmetry breaking; prove orbit coverage before using any exclusion. D9 C3-C7 remains a separate mandatory branch family.
5. Resume only after a small controlled benchmark materially improves certified SAT/UNSAT yield. No broad retry, no automatic schedule, no new workflow in this commit.
