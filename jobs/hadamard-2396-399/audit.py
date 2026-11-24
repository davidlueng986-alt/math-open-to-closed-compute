"""Check the original signs and the entire 399-point quotient by exact arithmetic."""

import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "hadamard-2396-diagonal"))
from check import EXTENSION, LENGTH, evaluate, original, paf, representatives, sign_input, unpack, words

QUOTIENT = 399
RESIDUES = {m % QUOTIENT for m in (1, -1, 64, -64, 106, -106)}
NEW_PAIRS = [s for s in range(1, 599) if s % QUOTIENT in RESIDUES]
SUBGROUPS = representatives((57, 63))
TARGET = sorted(set(SUBGROUPS) | set(NEW_PAIRS))


def audit(masks, scalar=False):
    legacy = evaluate(masks, "extend57", scalar=scalar)
    raw = original(masks)
    extended = [raw[s-1]+2 for s in TARGET]
    projected = [[sum(row[i::QUOTIENT]) for i in range(QUOTIENT)] for row in words(masks)]
    errors = [paf(projected, t) - (2390 if not t else -6) for t in range(200)]
    for t, error in enumerate(errors):
        total = 0
        for s in (t, t+399, t+798):
            if s:
                total += raw[min(s, LENGTH-s)-1] + 2
        if error != total:
            raise ValueError(f"projection and individual correlations disagree at {t}")
    def representative(t):
        return min((k*t) % QUOTIENT for k in RESIDUES)
    focus = {representative(s) for s in range(399) if s%19 == 0 or s%21 == 0} | {1}
    focus_score = 0
    for t in focus:
        unit = 12 if t%19 == 0 else 4
        if errors[t] % unit:
            raise ValueError("wrong divisibility in the selected quotient equations")
        focus_score += (errors[t]//unit)**2
    if len(NEW_PAIRS) != 9 or len(TARGET) != 67:
        raise ValueError("wrong target shifts")
    return {
        "quotient_energy": sum(v*v for v in errors),
        "quotient_zero_error": errors[0],
        "quotient_paf_at_one": errors[1]-6,
        "quotient_exact_nonzero_pairs": errors[1:].count(0),
        "focus_score": focus_score,
        "target_energy": sum(v*v for v in extended),
        "target_exact_pairs": extended.count(0),
        "previous_subgroup_exact_pairs": legacy["target_exact_shift_pairs"],
        "raw_energy": legacy["raw_energy"],
        "raw_paf_at_one": raw[0],
        "raw_paf_at_399": raw[398],
        "raw_exact_pairs": legacy["raw_exact_shift_pairs"],
        "raw_peak_error": legacy["raw_peak_error"],
    }


def key(category, r):
    if category == "quotient":
        return (r["quotient_energy"], r["raw_energy"])
    if category == "full":
        return (r["raw_energy"], r["quotient_energy"])
    if category == "balanced":
        return (r["raw_paf_at_399"] != -2, r["raw_energy"])
    if category == "extended":
        return (r["target_energy"], r["raw_energy"])
    raise KeyError(category)


def validate(record, scalar=True):
    stats = audit(record["negative_masks"], scalar)
    if any(value != record.get(key) for key, value in stats.items()):
        raise ValueError("stored statistics disagree with the sign masks")
    return stats


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("file", nargs="?", type=Path)
    args = p.parse_args()
    if args.file:
        data = json.loads(args.file.read_text())
        print(json.dumps({k: validate(r) for k,r in data["witnesses"].items()}, indent=2))
    else:
        print(json.dumps(audit(EXTENSION["negative_masks"], True), indent=2))
