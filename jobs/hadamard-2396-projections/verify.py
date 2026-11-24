"""Check complete 1197-sign certificates using only integer arithmetic."""

import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LENGTH = 1197
QUOTIENTS = (57, 63, 133)
PRIMARY_ORDERS = (7, 9, 19)


def words(masks):
    if len(masks) != 2:
        raise ValueError("two sign words required")
    rows = []
    for encoded in masks:
        mask = int(encoded, 16)
        if not 0 <= mask < 1 << LENGTH:
            raise ValueError("mask outside the 1197 positions")
        rows.append([1 - 2 * ((mask >> i) & 1) for i in range(LENGTH)])
    return rows


def paf(rows, shift):
    return sum(x * row[(i + shift) % len(row)] for row in rows for i, x in enumerate(row))


def original(masks):
    numbers = [int(v, 16) for v in masks]
    mask = (1 << LENGTH) - 1
    values = []
    for s in range(1, (LENGTH + 1) // 2):
        differences = sum(
            (word ^ (((word << s) & mask) | (word >> (LENGTH - s)))).bit_count()
            for word in numbers
        )
        values.append(2 * LENGTH - 2 * differences)
    return values


def representatives(orders):
    return [s for s in range(1, (LENGTH + 1) // 2) if any((q * s) % LENGTH == 0 for q in orders)]


def check(masks, margins):
    rows = words(masks)
    if list(map(sum, rows)) != [1, 1]:
        raise ValueError("wrong signs or normalization")
    if {int(key) for key in margins} != set(QUOTIENTS):
        raise ValueError("expected the 57-, 63- and 133-point margins")
    for q in QUOTIENTS:
        comp = [[sum(row[j::q]) for j in range(q)] for row in rows]
        if comp != margins[str(q)]:
            raise ValueError(f"wrong compression at {q}")
        m = LENGTH // q
        if [paf(comp, s) for s in range(q)] != [2396 - 2 * m] + [-2 * m] * (q - 1):
            raise ValueError(f"nonzero projection error at {q}")
    values = original(masks)
    triples = [sum(row[j] == row[j + 399] == row[j + 798] for j in range(399)) for row in rows]
    if 4 * sum(triples) - 798 != values[398] or values[398] != -2:
        raise ValueError("shift 399 failed")
    return {
        "raw_energy": sum((x + 2) ** 2 for x in values),
        "raw_exact_shift_pairs": values.count(-2),
        "raw_peak_error": max(abs(x + 2) for x in values),
        "raw_paf_at_one": values[0],
        "constant_triples": triples,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--signs", metavar="NAME", help="print a named pair as two lines of ±1")
    args = parser.parse_args()
    initial = json.loads((HERE / "witness.json").read_text())
    margins = initial["projections"]
    certificates = {"seed": initial, **json.loads((HERE / "original-search.json").read_text())}
    if args.signs:
        if args.signs not in certificates:
            parser.error("choose from " + ", ".join(certificates))
        for row in words(certificates[args.signs]["negative_masks"]):
            print(*row)
        return
    results = {}
    for name, record in certificates.items():
        masks = record["negative_masks"]
        stats = check(masks, margins)
        rows = words(masks)
        direct = [paf(rows, s) for s in range(1, (LENGTH + 1) // 2)]
        if direct != original(masks):
            raise ValueError("packed and scalar original correlations disagree")
        if name != "seed" and any(record[key] != value for key, value in stats.items()):
            raise ValueError(f"incorrect stored statistics for {name}")
        exact = representatives(record.get("subgroup_orders", ()))
        if any(direct[s - 1] != -2 for s in exact):
            raise ValueError(f"a claimed original subgroup fails for {name}")
        results[name] = {**stats, "checked_subgroup_shift_pairs": len(exact)}
    modes = {j * (LENGTH // q) for q in QUOTIENTS for j in range(1, q)}
    print(json.dumps({"projected_nontrivial_frequencies": len(modes), "original": results}, indent=2))


if __name__ == "__main__":
    main()
