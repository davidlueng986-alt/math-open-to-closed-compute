"""Recreate both subgroup certificates, including the two-error intermediate lift."""

import json
from pathlib import Path
import subprocess
import sys

from check import CERT, EXTENSION, SEED, evaluate, original, representatives, sign_input, unpack


def search(binary, mode, seed, coarse_steps, phase_steps, masks):
    proc = subprocess.run(
        [binary, mode, str(seed), str(coarse_steps), str(phase_steps)],
        input=sign_input(masks), text=True, stdout=subprocess.PIPE, check=True,
    )
    record = json.loads(proc.stdout)
    output = unpack(record)
    stats = evaluate(output, mode, scalar=True)
    if any(record[k] != stats[k] for k in ("coarse_score", "phase_score")):
        raise ValueError("search score disagrees with exact reconstruction")
    return output, stats


def main(binary):
    first, _ = search(binary, "both", 1210, 200000, 300000, SEED["negative_masks"])
    if first != CERT["negative_masks"]:
        raise ValueError("first search returned different signs")
    near, stats = search(binary, "extend57", 1250, 350000, 600000, first)
    raw = original(near)
    missed = {s: raw[s-1] for s in representatives((57, 63)) if raw[s-1] != -2}
    if stats["coarse_score"] or missed != {342: 10, 456: -14}:
        raise ValueError("shard-6 endpoint differs")
    final, counts = search(binary, "extend57", 710, 0, 350000, near)
    if final != EXTENSION["negative_masks"] or counts["target_energy"]:
        raise ValueError("extension search returned different signs")
    print(json.dumps({"intermediate_failed_shift_pairs": missed, "final": counts}, indent=2))


if __name__ == "__main__":
    main(str(Path(sys.argv[1]).resolve()))
