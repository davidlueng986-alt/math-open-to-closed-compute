# Jobs

Each job is a folder `jobs/<name>/`. Folders starting with `_` are templates and cannot be run.

| File | Required | What it does |
| --- | --- | --- |
| `run.sh` | yes | `run.sh SHARD SHARDS OUTDIR`: computes shard `SHARD` (0 to `SHARDS-1`) and writes `OUTDIR/result.json` |
| `setup.sh` | no | Installs what the job needs (`apt-get`, `pip`); runs before `run.sh` on every shard |
| `merge.py` | no | `merge.py SHARDS_DIR SUMMARY_DIR`: combines shard results, writes extra files to `SUMMARY_DIR`, exits non-zero if the combined result is wrong |

Guidelines:

- A shard must finish within the per-shard limit (330 minutes by default; GitHub stops every job at 6 hours). Size shards for about 5 hours or less, and split further rather than racing the limit.
- Partition deterministically from `SHARD` and `SHARDS` so any shard can be rerun alone and the shards provably cover the whole search.
- Keep `result.json` small. Large outputs stay in the shard's artifact (kept 7 days); the Free plan has 500 MB of artifact storage.
- A shard that times out leaves no `result.json`; `collect` lists it as missing and the run fails, so a gap is never mistaken for a complete search.
- Each runner has 4 vCPUs, 16 GB RAM and 14 GB of disk.
- Everything in a job, including its output, is public.
