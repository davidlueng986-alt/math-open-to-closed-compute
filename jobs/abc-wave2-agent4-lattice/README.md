# ABC Wave 2 Agent 4 — primitive relation normalization

Run `bash run.sh 0 1 OUT`. Python standard library suffices; use the SAT toolbox.

The verifier checks the exact gcd/lcm bound, relation normalization, height and radical inequalities, embeddings of primitive abc triples into prescribed fixed-base relation lattices, and a varying-base obstruction. All ranges and counts are recorded in `certificates.json`. It proves no infinite coefficient-radical estimate and does not resolve abc.

Mathematical proofs and remaining obligations: `research/ABC/wave2_agent4/REPORT.md` and `obligations.json` in the main repository. Source and certificate SHA256 are emitted in `result.json`; GitHub identifiers are populated only when actually run there.
