# ABC Wave 1 Agent 4: exact certificates and bounded lattice search

Run in SageMath 10.6 (the project's `math-compute-sage` container):

```sh
bash jobs/abc-wave1-agent4-triples/run.sh 0 1 out
```

The 1,345-seed manifest consists of one explicitly labeled Reyssat replay seed and 1,344 exploratory seeds: four bit scales (20,32,48,64), all 84 triples of distinct primes among 2,3,5,7,11,13,17,19,23, and four specified exponent offsets. Each integer relation lattice has rank two. LLL is run for every seed. BKZ with block size two is also run every 32 seeds and on the replay. BKZ-2 is not claimed to give an advantage over a two-dimensional lattice reduction.

Both signs of each relation are identified. Combinations of the two reduced basis rows use coefficients in [-2,2]. Each nonzero three-term relation is divided by its gcd and converted to a primitive positive abc triple. Complete factorizations are obtained with Sage proof enabled. Quality >8/5 is decided by exact integer powers, c^5 > rad(abc)^8, never by a floating logarithm. 256-bit real intervals are used for comparison with the reference record; an overlap is recorded as unresolved.

Every quality >8/5 hit, top 40 displayed candidates and constant witness gets a full certificate. A separate standard-library Python verifier uses integer arithmetic and trial-division primality to audit those certificates, with no Sage dependency. The entire finite candidate set also has a deterministic sorted-triple SHA-256 digest. No numerical search is claimed exhaustive over all triples.

For epsilon=1/100,1/10,1/2, exact integer powers certify rational brackets for c/R^(1+epsilon). The lower endpoint is a necessary lower bound for any global K_epsilon; the upper endpoint is ONLY an upper bound for that one finite triple's ratio. It is not a global K_epsilon upper bound.

The method is an implementation of Dokchitser's published LLL approach (2003/2004), not a new algorithm. Replay is intentionally separated from exploration. GitHub workflow evidence is supplied by the parent ABC Wave 1 manual-dispatch workflow.
