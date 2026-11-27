# ABC Wave 1 Agent 3: function-field transfer audit

Run `bash setup.sh`, then `bash run.sh 0 1 /tmp/abc-agent3-result`.

The single-shard job performs exact QQ-polynomial Wronskian/divisibility checks, fully factors 40 specializations of `T(T+1)` at powers of 2, and checks the scalar normalization shadow described in the research report. It writes `result.json` and `certificates.json` with hashes. It has no network access after dependency installation, no paid services, and no scheduled workflow.

Scope: the finite audit is CHECKED only when the run succeeds. It does not prove arithmetic abc, reconstruct IUT, or establish that the scalar shadow captures all IUT hypotheses. The infinite obstruction to degree-preserving radical specialization is proved separately in the research report. Runtime is normally under a minute with Python 3.11+ and SymPy 1.14.0; the parent workflow should use a modest timeout.
