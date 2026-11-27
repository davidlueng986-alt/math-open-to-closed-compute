# ABC Wave 2 verification orchestration

Explicitly authorized continuation of the six-agent ABC research. Source jobs verify their stated structural fragments and bounded computations, never full abc or an unresolved infinite estimate.

`abc-wave2.yml` runs only by workflow_dispatch. The exact-path push launcher validates `launch.json` and issues one workflow_dispatch with the repository GITHUB_TOKEN; it has no schedule and unrelated commits do not launch it. The same one-shot method was used in Wave 1 because this session has no direct workflow-dispatch connector operation.

Selections: all, math (agents1–5), agent1 through agent6. A matrix entry can be staged before its job is published; only dispatch a selection after every selected bundle is present. Containers are pinned to the digests verified in Wave1. Every verify job has a45-minute limit, launcher5minutes, publisher10minutes, all below the user ceiling6hours. No paid runners or resources.

The run preserves exact source hashes, result.json, logs and kernel output where applicable, and publishes them to the existing results branch under runs/abc-wave2/RUN_ID. Failure output remains evidence and is not replaced by an unrecorded success.
