# ABC Wave 2 — Agent 1 exact orbit-local audit

Research namespace: `research/ABC/wave2_agent1/` in `math-open-to-closed`.

```bash
bash jobs/abc-wave2-agent1-orbit-local/run.sh 0 1 /tmp/abc-wave2-agent1
```

Python 3.8+ standard library; no third-party dependencies. The orchestrator dispatches the audit through a manual GitHub Actions workflow. No paid services, scheduled workflows, or indefinite search are needed.

`result.json` reports source and canonical-certificate SHA256, exact counts and hosted identifiers. `certificates.json` contains the finite witnesses. Exhaustive trial division is restricted to differences <= 10^8. The run verifies finite instances of the written lemmas and the explicit varying-seed constructions; it does not prove the open infinite lifting-mass condition or the abc conjecture.
