"""Search the mixed subgroup of order 21 together with the three primary subgroups."""

import json
from pathlib import Path
import subprocess
import sys

PROJECT = Path(__file__).resolve().parent.parent / "hadamard-2396-projections"
sys.path.insert(0, str(PROJECT))
from verify import check, original, representatives, words

SHIFTS = representatives((7, 9, 19, 21))


def metrics(masks, margins):
    values = original(masks)
    gaps = {str(s): values[s-1] + 2 for s in SHIFTS if values[s-1] != -2}
    return {"target_energy": sum(d*d for d in gaps.values()), "remaining": gaps,
            **check(masks, margins)}


def trial(binary, masks, mode, seed, steps, margins):
    data = "\n".join(" ".join(map(str, row)) for row in words(masks)) + "\n"
    v = json.loads(subprocess.check_output([binary, str(seed), mode, str(steps)], input=data, text=True))
    out = [hex(int(row[::-1], 2)) for row in v["rows"]]
    result = {"negative_masks": out, **metrics(out, margins)}
    if v["shifts"] != SHIFTS or v["score"] != result["target_energy"]:
        raise ValueError("direct correlation check failed")
    return result


def main(binary, shard, shards, outfile):
    certs = json.loads((PROJECT / "original-search.json").read_text())
    margins = json.loads((PROJECT / "witness.json").read_text())["projections"]
    masks = certs["near21"]["negative_masks"]
    best = {"negative_masks": masks, **metrics(masks, margins)}
    log = []
    for restart in range(3):
        candidates = [best]
        for j, name in enumerate(("near21", "primary", "hybrid", "near21", "energy", "primary")):
            seed = 8851 + ((restart*6+j)*shards + shard)*37
            init = best["negative_masks"] if j in (0,3) else certs[name]["negative_masks"]
            steps = (32000, 800000, 700000, 150000, 500000, 1000000)[j]
            found = trial(binary, init, "axis21", seed, steps, margins)
            log.append([seed, steps, found["target_energy"]])
            candidates.append(found)
        # Try independent endpoints even when their four nonzero residuals have equal norm.
        distinct = {tuple(v["negative_masks"]): v for v in candidates}
        ranked = sorted(distinct.values(), key=lambda v: (v["target_energy"], v["raw_energy"]))
        for candidate in ranked[:3]:
            out = trial(binary, candidate["negative_masks"], "quad21", 1, 0, margins)
            log.append([1, 0, out["target_energy"]])
            if (out["target_energy"],out["raw_energy"]) < (best["target_energy"],best["raw_energy"]):
                best = out
            if not best["target_energy"]:
                break
        if not best["target_energy"]:
            break
    Path(outfile).write_text(json.dumps({"shard":shard,"shards":shards,"best":best,"log":log})+"\n")


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
