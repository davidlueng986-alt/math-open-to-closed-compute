"""Verify the partition and report counts in the original labelled coordinates."""
import json
import sys
from collections import Counter
from pathlib import Path

from search import base_classes, supports

VERDICTS = {"mod4", "row_norm", "shift_inconsistent", "affine_norm",
            "affine_exhausted", "unresolved", "exact_projection"}


def verify_projection(u, negative):
    rows = [[(1 if f < 3 else 2) if y == 0 else
             (-2 if (negative[f] >> y) & 1 else 2) if (u[f] >> y) & 1 else 0
             for y in range(149)] for f in range(4)]
    if any(n & ~s for n, s in zip(negative, u)):
        raise ValueError("a negative bit lies outside the support")
    for shift in range(149):
        actual = sum(row[j] * row[(j+shift) % 149] for row in rows for j in range(149))
        if actual != (599 if shift == 0 else 0):
            raise ValueError("invalid projection certificate")


def main(inputs, output):
    records = {}
    result_files = sorted(inputs.glob("shard-*/result.json"))
    for file in result_files:
        shard = json.loads(file.read_text())
        if shard["shards"] != len(result_files) or file.parent.name != f"shard-{shard['shard']}":
            raise ValueError("missing or misidentified shards")
        for row in shard["classes"]:
            mask = row["mask"]
            if mask in records:
                raise ValueError("duplicate base class")
            records[mask] = row
    expected = dict(base_classes())
    if set(records) != set(expected) or len(records) != 46 or sum(expected.values()) != 1820:
        raise ValueError("incomplete base partition")
    base_count, moved_count, representatives = Counter(), Counter(), Counter()
    survivors = []
    for mask, row in sorted(records.items()):
        weight = expected[mask]
        tally = Counter(row["moves"])
        if row["base_multiplicity"] != weight or sum(tally.values()) != 1776 or set(tally) - VERDICTS:
            raise ValueError("invalid tally")
        if row["base_status"] not in VERDICTS:
            raise ValueError("unknown base status")
        base_count[row["base_status"]] += weight
        u = supports(mask)
        if row["base_status"] in ("unresolved", "exact_projection"):
            if row["base_status"] == "exact_projection":
                verify_projection(u, [int(s, 16) for s in row["base_evidence"]["negative"]])
            survivors.append({"mask": mask, "move": None, "status": row["base_status"], **row["base_evidence"]})
        dispositions = Counter()
        assigned = set()
        for entry in row["survivors"]:
            f, y, g, z = entry["move"]
            key = (f, y, g, z)
            if key in assigned or not (u[f] >> y) & 1 or (u[g] >> z) & 1 or min(y,z) == 0:
                raise ValueError("invalid move")
            assigned.add(key)
            dispositions[entry["status"]] += 1
            if entry["status"] == "exact_projection":
                new = u.copy()
                new[f] ^= 1 << y
                new[g] ^= 1 << z
                verify_projection(new, [int(s, 16) for s in entry["negative"]])
            survivors.append({"mask": mask, **entry})
        if dispositions != Counter({k: tally[k] for k in ("exact_projection", "unresolved") if tally[k]}):
            raise ValueError("survivor count disagrees")
        for key, count in tally.items():
            moved_count[key] += weight * 37 * count
            representatives[key] += count
    if sum(moved_count.values()) != 119595840 or sum(representatives.values()) != 81696:
        raise ValueError("move coverage mismatch")
    summary = {"prime": 149, "group_generator": 2, "base_labelled": dict(base_count),
               "one_exchange_labelled": dict(moved_count), "move_representatives": dict(representatives),
               "base_classes": len(records), "base_count": sum(base_count.values()),
               "one_exchange_count": sum(moved_count.values()), "survivor_representatives": len(survivors)}
    output.mkdir(parents=True, exist_ok=True)
    (output / "census.json").write_text(json.dumps(summary, indent=2)+"\n")
    (output / "survivors.json").write_text(json.dumps(survivors)+"\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
