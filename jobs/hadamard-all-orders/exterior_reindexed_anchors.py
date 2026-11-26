"""Replay seven through nine named exact Sylvester pairs in reindexed exterior stacks."""

from collections import Counter
import json
from pathlib import Path

from exterior_fold_trade import omitted_residual
from exterior_mod16_invariant import decode, low_high_moments
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture


EXPECTED = {
    "seven": (7, 482, (198, 160, 274, 284, 252), 475, (549, 549), [1193, 930, 286, 38, 26], 3),
    "eight": (8, 483, (198, 160, 272, 284, 252), 475, (560, 560), [1193, 902, 316, 41, 24], 6),
    "nine": (9, 483, (198, 160, 272, 284, 252), 475, (560, 560), [1193, 916, 285, 36, 25], 4),
}


def check_profile(name, data, source):
    factors = json.loads((source / "exterior_exact_factor_witnesses.json").read_text())
    previous = json.loads((source / "exterior_mod16_invariant_witness.json").read_text())
    closed = json.loads((source / "exterior_fold_trade_exact_witness.json").read_text())["lower"]
    reference = factors[7]["lower"]
    upper_text, new = previous["upper"], data["lower"]
    top, lower, upper_margins, lower_margins = gram_fixture()
    half = BOTTOM // 2
    masks, original, closed_masks = ([int(x, 32) for x in s] for s in (new, reference, closed))
    require(len(masks) == len(original) == len(closed_masks) == BOTTOM, "all physical lower masks present")
    require([s.bit_count() for s in masks] == [s.bit_count() for s in lower_margins]
            and [int(x, 32).bit_count() for x in upper_text] == [s.bit_count() for s in upper_margins],
            "all physical row margins")
    old_columns, new_columns, upper = map(decode, (reference, new, upper_text))
    require(all((a.bit_count(), (a >> half).bit_count()) == (b.bit_count(), (b >> half).bit_count())
                for a, b in zip(old_columns, new_columns, strict=True)), "all exact lower half weights")
    require(all(a.bit_count() + b.bit_count() == ORDER // 2
                for a, b in zip(upper, new_columns, strict=True)), "all exact outer column weights")
    top_gram = correlations(upper, upper, TOP)
    bottom_gram = correlations(new_columns, new_columns, BOTTOM)
    require(all(top_gram[i][j] + bottom_gram[i][j] == ORDER * (i == j)
                for i in range(WIDTH) for j in range(WIDTH)), "exact new-column Gram")
    dots = correlations(lower, new_columns, BOTTOM)
    old_dots = correlations(lower, old_columns, BOTTOM)
    beta = [dots[i] for i in LOWER_OMISSIONS]
    expected_beta = [[-2 * v for v in row] for row in factors[7]["factor"]]
    require(beta == [old_dots[i] for i in LOWER_OMISSIONS] and beta[1:] == expected_beta,
            "all 35 original exact omitted dots")
    alpha = correlations(top[1:3], upper, TOP)
    require(all(v == 0 for row in omitted_residual(alpha, beta, top_gram) for v in row), "all 25 exact omitted Gram entries")

    def folds(rows):
        return [a ^ b for a, b in zip(rows[:half], rows[half:], strict=True)]

    current_fold, old_fold, closed_fold = map(folds, (masks, original, closed_masks))
    difference = [a ^ b for a, b in zip(current_fold, old_fold, strict=True)]
    changed_bases = sum(bool(v) for v in difference)
    distances = tuple(sum(v >> j & 1 for v in difference) for j in range(WIDTH))
    from_closed = sum(a != b for a, b in zip(current_fold, closed_fold, strict=True))
    changed_indices = [any((a - b) % 8 for a, b in zip(y, z, strict=True))
                       for y, z in zip(dots, old_dots, strict=True)]
    index_changes = (sum(changed_indices[:half]), sum(changed_indices[half:]))
    desired_pairs, desired_bases, desired_distances, desired_closed, desired_indices, desired_counts, desired_special = EXPECTED[name]
    require((changed_bases, distances, from_closed, index_changes)
            == (desired_bases, desired_distances, desired_closed, desired_indices), "reindexed physical fold metrics")

    upper_dots = dict(enumerate(correlations(top[3:], upper, TOP), start=3))
    lower_dots = {i: [-v for v in row] for i, row in enumerate(dots) if i not in LOWER_OMISSIONS}
    require(len(data["anchors"]) == len({r[0] for r in data["anchors"]}) == desired_pairs,
            "distinct complete Sylvester pairs")
    anchors = {}
    for base, plus, minus in data["anchors"]:
        require(0 <= base < half and base in lower_dots and base + half in lower_dots,
                "both lower partners are retained")
        anchors[base] = plus
        anchors[base + half] = minus
    require(len(anchors) == len(set(anchors.values())) and anchors.get(313) == 592 and anchors.get(913) == 577,
            "distinct upper partners and the named boundary pair")
    require(all(lower_dots[i] == upper_dots[j] for i, j in anchors.items()), "all named integer five-vectors")
    require(low_high_moments(list(upper_dots.values())) == low_high_moments(list(lower_dots.values())),
            "absolute mixed-bit consistency")

    used_upper = set(anchors.values())
    remaining_upper = [row for i, row in upper_dots.items() if i not in used_upper]
    remaining_lower = [row for i, row in lower_dots.items() if i not in anchors]
    counts = []
    for modulus in (8, 16, 32, 64, None):
        key = tuple if modulus is None else lambda row: tuple(v % modulus for v in row)
        a, b = Counter(map(key, remaining_upper)), Counter(map(key, remaining_lower))
        counts.append(sum((a & b).values()) + len(anchors))
    special = sum(tuple(v % 16 for v in row) == (6, 4, 12, 14, 14) for row in lower_dots.values())
    require(counts == desired_counts and special == desired_special, "all named matches extend to the joint modulo-eight pairing")
    print(f"n=2396 reindexed exterior anchors: {len(anchors) // 2} exact Sylvester pairs, "
          f"joint matches {tuple(counts)}, {distances[1]} second-fold changes, "
          f"{sum(index_changes)} indexed mod8 changes, special count {special}")
    return current_fold, [tuple(v % 8 for v in row) for row in dots], anchors


if __name__ == "__main__":
    directory = Path(__file__).resolve().parent
    data = json.loads((directory / "exterior_reindexed_anchors.json").read_text())
    if data.get("reference") != 8:
        raise ValueError("the physical anchor profiles use the eighth exact factor")
    checked = {case: check_profile(case, data[case], directory) for case in EXPECTED}
    eight_fold, eight_indexed, eight_anchors = checked["eight"]
    nine_fold, nine_indexed, nine_anchors = checked["nine"]
    require(eight_fold == nine_fold and eight_indexed == nine_indexed, "nine anchors use the same physical fold and every indexed residue")
    require(eight_anchors.items() < nine_anchors.items(), "the original eight exact pairs remain fixed")
