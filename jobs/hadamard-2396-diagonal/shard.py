"""Attempt the order-57 extension and check every output against the original signs."""

import json
from pathlib import Path
import subprocess
import sys

from check import CERT, evaluate, sign_input, unpack


def main(binary, shard, output):
    initial = sign_input(CERT["negative_masks"])
    records = []
    for offset in range(6):
        seed = 1211 + 6*shard + offset
        run = subprocess.run(
            [binary, "extend57", str(seed), "350000", "600000"], input=initial,
            text=True, stdout=subprocess.PIPE, check=True,
        )
        result = json.loads(run.stdout)
        masks = unpack(result)
        stats = evaluate(masks, "extend57")
        if any(result[key] != stats[key] for key in ("coarse_score", "phase_score")):
            raise ValueError("search and independent objective disagree")
        records.append({"seed": seed, "negative_masks": masks, **stats})
        if stats["target_energy"] == 0:
            break
    best = min(records, key=lambda r: (r["target_energy"], r["raw_energy"]))
    evaluate(best["negative_masks"], "extend57", scalar=True)
    for record in records:
        if record is not best:
            del record["negative_masks"]
    Path(output).write_text(json.dumps({"shard": shard, "trials": records}, indent=2) + "\n")


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), sys.argv[3])
