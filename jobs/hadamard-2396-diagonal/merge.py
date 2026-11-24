"""Recheck the best original order-63/57 candidate from each shard."""

import json
from pathlib import Path
import sys

from check import evaluate


def main(shards, output):
    winners = []
    total = 0
    for file in sorted(shards.glob("shard-*/result.json")):
        data = json.loads(file.read_text())
        trials = data["trials"]
        if not trials or any(r["seed"] != 1211 + 6*data["shard"] + i for i, r in enumerate(trials)):
            raise ValueError(f"wrong seed schedule in {file}")
        total += len(trials)
        best = min(trials, key=lambda r: (r["target_energy"], r["raw_energy"]))
        verified = evaluate(best["negative_masks"], "extend57", scalar=True)
        if any(best[k] != v for k, v in verified.items()):
            raise ValueError(f"inconsistent subgroup search result in {file}")
        winners.append(best)
    best = min(winners, key=lambda r: (r["target_energy"], r["raw_energy"]))
    report = {"trials": total, "shards": len(winners), "target_orders": [57, 63], "best": best,
              "shards_with_zero_target_error": sum(r["target_energy"] == 0 for r in winners)}
    (output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{total} trials, best squared subgroup error {best['target_energy']}")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
