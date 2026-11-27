# ABC Wave 3 Agent 1 — quartic root reduction

Standard-library Python exact finite checks. Expected run well below one minute; no external dependency.

```
bash jobs/abc-wave3-agent1-quartic-root/run.sh 0 1 /tmp/abc-wave3-agent1
```

Output: result.json and certificates.json. Every result explicitly retains original_abc_closed=false. Mathematical proof is in research/ABC/wave3_agent1/REPORT.md in the main repository. This verifies finite implementations and parameter algebra; it does not prove the open ROOT estimate.
