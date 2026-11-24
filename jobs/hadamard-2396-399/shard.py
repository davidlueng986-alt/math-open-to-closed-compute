"""Search all quotient equations, the full objective, and the 67 prescribed pairs."""

import json
from pathlib import Path
import subprocess
import sys

from audit import EXTENSION, audit, key, sign_input, unpack


def run(binary, args, masks):
    result = subprocess.run([str(binary), *map(str, args)], input=sign_input(masks),
                            text=True, capture_output=True, check=True)
    output = json.loads(result.stdout)
    m = unpack(output)
    stats = audit(m)
    if any(output[k] != stats[k] for k in output.keys() & stats.keys()):
        raise ValueError("incremental score disagrees with scalar quotient or packed original score")
    return {"negative_masks": m, **stats}


def main(bin_dir, shard, output):
    bins = {name: bin_dir/name for name in ("search", "phases", "raw")}
    start = EXTENSION["negative_masks"]
    pivot = run(bins["search"], [514, 0, 0], start)
    first = run(bins["phases"], [730, 400000, 1], pivot["negative_masks"])
    if first["target_energy"]:
        raise ValueError("failed positive control on all 67 shift pairs")
    winners = dict.fromkeys(("quotient", "full", "balanced", "extended"), first)
    exact_quotient = pivot
    trials = []
    for i in range(7):
        seed = 4200 + 7*shard + i
        results = []
        def trial(name, args, source):
            r = run(bins[name], args, source)
            r["seed"] = seed
            r["stage"] = name
            results.append(r)
            return r
        quotient = trial("search", [seed, 800000, 0],
                         winners["quotient"]["negative_masks"] if i%2 else start)
        trial("raw", [seed, "free", 1150000, 0],
              winners["full"]["negative_masks"] if i%2 else quotient["negative_masks"])
        trial("raw", [seed, "balanced", 850000, 0],
              winners["balanced"]["negative_masks"] if i%2 else start)
        focus = trial("search", [seed, 210000, 8, 210000, 100, 320000, 1000, 0, 0],
                      quotient["negative_masks"])
        if not focus["focus_score"] and focus["quotient_energy"] < exact_quotient["quotient_energy"]:
            exact_quotient = focus
        source = winners["extended"]["negative_masks"] if i%2 else exact_quotient["negative_masks"]
        near = trial("raw", [seed, "fixed", 230000, 2, "fixed", 160000, 25, "fixed", 200000, 280], source)
        trial("phases", [seed, 350000, 1], near["negative_masks"])
        for category in winners:
            winners[category] = min([winners[category], *results], key=lambda r: key(category,r))
        trials.append({"seed": seed, "minimum_quotient_energy": min(r["quotient_energy"] for r in results),
                       "minimum_raw_energy": min(r["raw_energy"] for r in results),
                       "minimum_target_energy": min(r["target_energy"] for r in results)})
    output.write_text(json.dumps({"shard": shard, "trials": trials, "witnesses":winners}, indent=2)+"\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]), int(sys.argv[2]), Path(sys.argv[3]))
