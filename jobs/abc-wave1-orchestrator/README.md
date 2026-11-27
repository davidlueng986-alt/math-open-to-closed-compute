# ABC Wave 1 manual dispatch bridge

The user explicitly authorized six public GitHub Actions verification jobs and prohibited paid resources and schedules. The available GitHub connector can write files and read Actions evidence but exposes no workflow-dispatch action; the cloud browser has no signed-in GitHub session.

An explicit commit to `launch.json` invokes a five-minute one-shot launcher, which calls GitHub's `workflow_dispatch` endpoint for `abc-wave1.yml` using the runner's normal repository-scoped `GITHUB_TOKEN`. The verifier itself is dispatch-only. There are no schedules, external credentials, recursive triggers or paid resources. Only an intentional change to this exact launch file starts the launcher; other repository commits do not.

Verification jobs have a 45-minute ceiling, publish exact source and evidence, and keep ABC unresolved. The launcher grants only the temporary Actions write permission necessary for the requested dispatch and does not alter repository access controls.
