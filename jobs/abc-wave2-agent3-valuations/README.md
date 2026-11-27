# ABC Wave 2 Agent 3 — valuation compensation

Toolbox: `sat` (Python standard library only). No external downloads or paid resources.

```bash
bash jobs/abc-wave2-agent3-valuations/run.sh 0 1 /tmp/abc-wave2-agent3
```

The job enumerates primitive positive triples with `a <= b`, `c <= 1200`, verifies exact factorization compensation identities, the cube-free global height lemma, a power-free tradeoff, and the balanced/moderate/thin partition and conditional composition at epsilon `1/6`. All checks use integer arithmetic.

`result.json` is a finite certificate. The general claims are supported by written proofs in `research/ABC/wave2_agent3/REPORT.md`; the two open estimates are not proved by this job. No Lean verification is claimed here.
