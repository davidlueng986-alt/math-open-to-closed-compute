# math-open-to-closed-compute

Open, reproducible computations for the Math Open-to-Closed research project, run on GitHub-hosted runners. A job is split into independent shards that run in parallel; their results are merged and committed to the `results` branch.

**Everything here is public:** code, inputs, logs and results.

The Hadamard project records order-2396 sign certificates, both routes to a definite answer for the full conjecture, and research assignments with explicit proof obligations. [Research log](HADAMARD.md) · [Full closure DAG](jobs/hadamard-all-orders/closure-dag/README.md) · [Agent task list](jobs/hadamard-all-orders/closure-dag/TASKS.md)

## Run a job

1. **Actions** tab → **sharded-run** → **Run workflow**.
2. Choose the job (a folder under `jobs/`), the number of shards (1–256), the per-shard time limit and how many shards run at once.
3. When the run finishes, the merged summary is in `results/runs/<job>/<run id>/` on the `results` branch, and as the run's `summary` artifact (kept 30 days). Each shard's own output is a `shard-<i>` artifact (kept 7 days).

Start with `selftest`: it counts the primes up to 10^7 across the shards and checks the total against π(10^7) = 664,579, so it tests the splitting and the merge end to end.

The workflow only runs when started by hand. A run fails if any shard is missing or the job's merge check fails.

## Add a job

Copy `jobs/_template/` to `jobs/<name>/` and follow [`jobs/README.md`](jobs/README.md).

## Limits

GitHub-hosted runners for public repositories are free. Per the [Actions limits](https://docs.github.com/en/actions/reference/limits) and [runner reference](https://docs.github.com/en/actions/reference/runners/github-hosted-runners):

- 6 hours per job; this workflow's default per-shard limit is 330 minutes
- 256 jobs per matrix, so at most 256 shards per run
- 20 concurrent jobs on the Free plan
- 4 vCPUs, 16 GB RAM, 14 GB SSD per runner
- 500 MB of artifact storage on the Free plan

## Terms

GitHub's [terms for Actions](https://docs.github.com/en/site-policy/github-terms/github-terms-for-additional-products-and-features#actions) say that GitHub-hosted runners should not be used for activity unrelated to the production, testing, deployment or publication of the software project in the repository, nor in a way that places a disproportionate burden on GitHub's servers. Keep the code that runs here in this repository, as a real open project, and keep runs proportionate. Misuse can lead to jobs being stopped, Actions being restricted, or the repository being disabled.

## License

MIT; see [LICENSE](LICENSE).
