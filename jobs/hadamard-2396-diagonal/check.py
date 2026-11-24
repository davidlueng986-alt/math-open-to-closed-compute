"""Verify length-1197 signs, projections, multiplier and both search objectives."""

import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "hadamard-2396-projections"))
from verify import LENGTH, QUOTIENTS, original, paf, representatives, words  # noqa: E402

SEED = json.loads((HERE / "seed.json").read_text())
CERT = json.loads((HERE / "certificate.json").read_text())
EXTENSION = json.loads((HERE / "extension.json").read_text())
CRT = {(i % 63, i % 19): i for i in range(LENGTH)}
GROUPS = {"both": (19, 63), "extend57": (57, 63)}


def sign_input(masks):
    return "".join(" ".join(map(str, row)) + "\n" for row in words(masks))


def unpack(result):
    rows = result["rows"]
    if len(rows) != 2 or any(len(r) != LENGTH or set(r) - {"0", "1"} for r in rows):
        raise ValueError("expected two complete negative-bit strings")
    return [hex(int(r[::-1], 2)) for r in rows]


def exact_quotient(value, divisor):
    result, remainder = divmod(value, divisor)
    if remainder:
        raise ValueError(f"residue {value} is incompatible with division by {divisor}")
    return result


def evaluate(masks, mode, *, scalar=False):
    rows = words(masks)
    if [sum(row) for row in rows] != [1, 1]:
        raise ValueError("both words must be normalized")
    if any(row[i] != row[463 * i % LENGTH] for row in rows for i in range(LENGTH)):
        raise ValueError("multiplier 463 fails")
    for q in QUOTIENTS:
        projected = [[sum(row[i::q]) for i in range(q)] for row in rows]
        if projected != SEED["projections"][str(q)]:
            raise ValueError(f"wrong {q}-point margins")
        m = LENGTH // q
        if [paf(projected, s) for s in range(q)] != [2396 - 2*m] + [-2*m] * (q-1):
            raise ValueError(f"wrong {q}-point autocorrelations")
    raw = original(masks)
    if scalar and raw != [paf(rows, s) for s in range(1, 599)]:
        raise ValueError("scalar and packed autocorrelations disagree")

    def at(x, y):
        i = CRT[x % 63, y % 19]
        return raw[min(i, LENGTH-i)-1] if i else 2*LENGTH

    def collapsed(x, y):
        return sum(at(x + 21*k, y) for k in range(3))

    coarse = [exact_quotient(collapsed(t, 0) - (2390 if t == 0 else -6), 12)
              for t in range(11)]
    phase = [exact_quotient(at(t, 0) + 2, 12) for t in range(3, 31, 3)]
    phase += [exact_quotient(at(0, y) + 2, 4) for y in (1, 2, 4)]
    if mode == "extend57":
        coarse += [exact_quotient(collapsed(0, y) + 6, 4) for y in (1, 2, 4)]
        phase += [exact_quotient(at(21, y) + 2, 4) for y in (1, 2, 4, 5, 8, 10)]

    target = representatives(GROUPS[mode])
    target_errors = [raw[s-1] + 2 for s in target]
    target_energy = sum(e*e for e in target_errors)
    if (target_energy == 0) != (not any(coarse) and not any(phase)):
        raise ValueError("two-stage equations disagree with original subgroup equations")
    triples = [sum(row[j] == row[j+399] == row[j+798] for j in range(399)) for row in rows]
    if raw[398] != 4*sum(triples) - 798:
        raise ValueError("triple-count identity failed")
    return {
        "coarse_score": sum(e*e for e in coarse),
        "phase_score": sum(e*e for e in phase),
        "target_energy": target_energy,
        "target_shift_pairs": len(target),
        "target_exact_shift_pairs": target_errors.count(0),
        "raw_energy": sum((v+2)**2 for v in raw),
        "raw_exact_shift_pairs": raw.count(-2),
        "raw_peak_error": max(abs(v+2) for v in raw),
        "raw_paf_at_one": raw[0],
        "constant_triples": triples,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--signs", choices=["seed", "certificate", "extension"])
    parser.add_argument("--replay", type=Path, help="check the exact output of the seed-1210 search")
    args = parser.parse_args()
    if args.signs:
        sys.stdout.write(sign_input({"seed": SEED, "certificate": CERT, "extension": EXTENSION}[args.signs]["negative_masks"]))
        return
    if args.replay and unpack(json.loads(args.replay.read_text())) != CERT["negative_masks"]:
        raise ValueError("search replay returned different signs")
    report = {}
    for data, mode in ((CERT, "both"), (EXTENSION, "extend57")):
        stats = evaluate(data["negative_masks"], mode, scalar=True)
        if (data["subgroup_orders"] != list(GROUPS[mode]) or stats["target_energy"] or
                any(stats[k] != data[k] for k in stats.keys() & data.keys())):
            raise ValueError(f"certificate discrepancy for {mode}")
        report[mode] = stats
    for data in [SEED, CERT, EXTENSION]:
        if data["length"] != LENGTH or data["multiplier"] != 463:
            raise ValueError("certificate header mismatch")
    initial = evaluate(SEED["negative_masks"], "both", scalar=True)
    if sum(initial["constant_triples"]) != 199:
        raise ValueError("seed fails the order-three equation")
    modes = {j*(LENGTH//q) for q in QUOTIENTS for j in range(1, q)}
    print(json.dumps({"projected_frequencies": len(modes), **report}, indent=2))


if __name__ == "__main__":
    main()
