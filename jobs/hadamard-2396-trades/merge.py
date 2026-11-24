"""Recalculate every shard's best result, then keep the best mixed-subgroup certificate."""

import json
import sys
from pathlib import Path

from search import PROJECT, metrics
from verify import LENGTH, original, paf, words


def main(source, output):
    margins = json.loads((PROJECT / "witness.json").read_text())["projections"]
    files = sorted(source.glob("shard-*/result.json"))
    records = []
    for f in files:
        result = json.loads(f.read_text())
        idx, count = result["shard"], result["shards"]
        if count != len(files) or f.parent.name != f"shard-{idx}":
            raise ValueError("missing or misplaced shard")
        v = result["best"]
        calc = metrics(v["negative_masks"], margins)
        if any(v[k] != value for k, value in calc.items()):
            raise ValueError("stored statistics disagree")
        rows = words(v["negative_masks"])
        if original(v["negative_masks"]) != [paf(rows, s) for s in range(1, (LENGTH + 1)//2)]:
            raise ValueError("independent scalar shifts disagree")
        records.append({**v, "shard": idx})
    best = min(records, key=lambda v: (v["target_energy"], v["raw_energy"], v["shard"]))
    summary = {"best":best, "subgroup_orders":[7,9,19,21],
               "shard_target_energies":{v["shard"]:v["target_energy"] for v in records}}
    (output / "results.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(f"22-shift energy {best['target_energy']}, full energy {best['raw_energy']}")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
