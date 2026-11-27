# ABC Wave 3 Agent 6 — independent frozen-snapshot audit

This is a standard-library Python metadata and logical-interface audit, not a mathematical proof checker or Lean formalization. It independently recomputes each declared route frontier without importing the canonical frontier implementation. It fails if the frozen source digests change, an open core estimate is promoted, an open antecedent is lost, a live transitive proof dependency is FAILED, proof dependencies are cyclic, the ROOT-only frontier differs from `{W2-A2-ROOT-BOUND}`, or any original-target route is closed.

The `snapshot/` tree contains the exact reviewed source files and canonical DAG/frontier. `snapshot-lock.json` binds every audit input by SHA256. `reviewed-files.json` binds the separate mathematical review's source files. The result records both sets of hashes and the actual Actions run and compute commit when hosted.

Run `bash run.sh 0 1 /absolute/output/path`. A successful process earns only `CHECKED` for this defined audit scope. It does not prove ROOT, GROWTH, or abc.

The initial task preparation does not claim this job has been dispatched. A successful hosted receipt must be attached by the orchestrator after observing the run and downloading its artifact.
