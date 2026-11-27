# ABC Wave 1 Agent 1: exact Frey checks

Run `bash setup.sh` then `bash run.sh 0 1 /tmp/abc-agent1-output`.

The script checks symbolic Weierstrass identities, both parity patterns in every coprime positive triple with c <= 60, two signed squaring transforms, explicit epsilon conversions, and a family disproving a naive subpolynomial-j lemma. Sage is used for an additional 240 exact minimal-model/conductor checks when available. `result.json` explicitly records whether Sage ran; no skipped check is reported as passed.

This job proves no new abc bound. Its finite checks support the universal elementary arguments in `math-open-to-closed/research/ABC/wave1_agent1/REPORT.md` and protect the reduction from normalization mistakes.

No paid resources, no scheduling. Expected runtime is seconds to a few minutes; use a manual workflow with a timeout below six hours.
