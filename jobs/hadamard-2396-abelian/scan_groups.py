"""Search both abelian group laws with the remaining candidate multiplier groups."""

import json
from pathlib import Path
import subprocess
import sys

from audit_group import N, audit, groups, words

START = json.loads(Path(__file__).with_name("start.json").read_text())


def search(binary, law, group, seed, schedule, source=None):
    lines = [str(len(group)), " ".join(map(str, group)), "random" if source is None else "signs"]
    if source is not None:
        lines.extend(" ".join(map(str, row)) for row in words(source["negative_masks"]))
    proc = subprocess.run([str(binary), law, str(seed), *map(str, schedule)],
                          input="\n".join(lines)+"\n", text=True, capture_output=True, check=True)
    result = json.loads(proc.stdout)
    if len(result["rows"]) != 2 or any(len(row) != N or set(row)-{"0","1"} for row in result["rows"]):
        raise ValueError("invalid output bits")
    masks = [hex(int(row[::-1], 2)) for row in result["rows"]]
    stats = audit(masks, law, group, scalar=False)
    if any(result[name] != stats[name] for name in ("raw_energy","word_orbits","lag_classes")):
        raise ValueError("orbit search score disagrees with the original correlations")
    return {"law":law, "group":list(group), "negative_masks":masks, "seed":seed, **stats}


def better(old, new):
    def score(r):
        return r["raw_energy"], r["raw_peak_error"], -r["raw_exact_pairs"]
    return new if old is None or score(new) < score(old) else old


def main(binary, shard, output):
    entries = []
    for law_index,law in enumerate(("cyclic","plane")):
        def explore(group, batch, starts, steps, kicks, cap, initial=None):
            best = initial
            for k in range(starts):
                seed = 130000 + 1000*shard + 400*law_index + 40*batch + k
                schedule = [steps, (260,480,700,390)[k%4], (25000,45000,75000)[k%3],
                            200000, 140, 30000]
                if kicks:
                    schedule += [-kicks, 3+k%5, cap]
                source = best if k%3 == 1 or initial is not None else None
                r = search(binary, law, group, seed, schedule, source)
                best = better(best, r)
            entries.append({"batch":batch,"attempts":starts,"witness":best})
            return best
        high = explore(groups(9)[shard%18], 0, 12, 1400000, 4, 128)
        middle = explore(groups(3)[shard%12], 1, 5, 950000, 1, 72)
        warm = {**START, "law":law, "group":START["group"], "seed":"start",
                **audit(START["negative_masks"],law,START["group"],scalar=False)}
        diagonal = explore(tuple(START["group"]), 2, 3, 850000, 2, 80, warm)
        initial = better(better(high, middle), diagonal)
        unrestricted = {**initial, "group":[1],
                        **audit(initial["negative_masks"],law,[1],scalar=False)}
        explore((1,), 3, 2, 450000, 0, 0, unrestricted)
    output.write_text(json.dumps({"shard":shard,"entries":entries},indent=2)+"\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), int(sys.argv[2]), Path(sys.argv[3]))
