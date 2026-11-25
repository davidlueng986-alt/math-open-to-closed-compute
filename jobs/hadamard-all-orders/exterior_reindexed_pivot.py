"""Replay the next capacity separator for the reindexed nine-pair exterior fold."""

from collections import Counter
import json
from pathlib import Path

from exterior_fold_trade import omitted_residual
from exterior_fold_coordinates import fold, plus_capacity, residue
from exterior_mod16_invariant import decode, low_high_moments
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture
from verify import paley


INDEX = 18
SECOND = 1


def priced_fold_changes(rows, index, new_column, price):
    half = BOTTOM // 2
    source = paley(half - 1)[index]
    folds = fold(rows)
    weight = sum(x >> new_column & 1 for x in rows)
    total = price * weight
    changes = []

    def bits(mask):
        size = mask.bit_count()
        return (0,) if size == 0 else (1,) if size == WIDTH else (0, 1)

    for r, old in enumerate(folds):
        sign = 2 * (source >> r & 1) - 1
        local = [max(sign * (2 - 2 * (a + b)) - price * (a + b)
                     for a in bits(rows[r]) for b in bits(rows[r + half]) if a ^ b == state)
                 for state in (0, 1)]
        f = old >> new_column & 1
        total += local[f]
        changes.append(local[f ^ 1] - local[f])
    return total, changes


def check_witness(here, reference, reference_anchors, upper, top, lower, upper_dots, label):
    fixture = json.loads((here / "exterior_reindexed_pivot_witness.json").read_text())
    half = BOTTOM // 2
    old_rows = [int(v, 32) for v in reference]
    rows = [int(v, 32) for v in fixture["lower"]]
    require(len(rows) == BOTTOM and all(a.bit_count() == b.bit_count()
                                    for a, b in zip(rows, old_rows, strict=True)), "all physical row margins")
    new_columns = decode(fixture["lower"])
    old_columns = decode(reference)
    require(all(a.bit_count() == b.bit_count() and (a >> half).bit_count() == (b >> half).bit_count()
                for a, b in zip(new_columns, old_columns, strict=True)), "all exact half and global weights")
    upper_gram = correlations(upper, upper, TOP)
    bottom_gram = correlations(new_columns, new_columns, BOTTOM)
    require(all(upper_gram[i][j] + bottom_gram[i][j] == ORDER * (i == j)
                for i in range(WIDTH) for j in range(WIDTH)), "all exact new/new orthogonalities")
    new_dots = correlations(lower, new_columns, BOTTOM)
    old_dots = correlations(lower, old_columns, BOTTOM)
    beta = [new_dots[i] for i in LOWER_OMISSIONS]
    require(beta == [old_dots[i] for i in LOWER_OMISSIONS], "all 35 precise original omitted projections")
    factors = json.loads((here / "exterior_exact_factor_witnesses.json").read_text())
    require(beta[1:] == [[-2 * x for x in row] for row in factors[7]["factor"]], "exact omitted factor eight")
    alpha = correlations(top[1:3], upper, TOP)
    require(all(x == 0 for row in omitted_residual(alpha, beta, upper_gram) for x in row), "all exact omitted Gram entries")
    fold_xors = [a ^ b for a, b in zip(fold(rows), fold(old_rows), strict=True)]
    changes = tuple(sum(v >> j & 1 for v in fold_xors) for j in range(WIDTH))
    reindexed = sum(residue(a) != residue(b) for a, b in zip(new_dots, old_dots, strict=True))
    require((sum(a != b for a, b in zip(rows, old_rows, strict=True)), sum(bool(v) for v in fold_xors),
             changes, sum(bool((a ^ b) & (1 << SECOND)) for a, b in zip(rows, old_rows, strict=True)), reindexed)
            == (555, 419, (194, 0, 222, 236, 248), 8, 1022), "the entire second fold is unchanged")
    require(len(reference_anchors) == 9 and all(new_dots[i][SECOND] == old_dots[i][SECOND]
                for base, _, _ in reference_anchors for i in (base, base + half)),
            "all 18 prior anchor dots preserved in the second coordinate")

    require(fixture["anchors"] == [[12, 506, 313], [14, 128, 277], [18, 588, 77], [313, 592, 577]], "prescribed retained plus/minus partner indices")
    anchors = {i: j for base, a, b in fixture["anchors"] for i, j in ((base, a), (base + half, b))}
    signed = {i: tuple(-v for v in row) for i, row in enumerate(new_dots) if i not in LOWER_OMISSIONS}
    high = dict(enumerate(upper_dots, start=3))
    require(len(set(anchors.values())) == 8 and all(signed[i] == tuple(high[j]) for i, j in anchors.items()),
            "the four complete Sylvester pairs cancel exactly")
    require(signed[18] == (10, -48, 16, 6, 18) and signed[618] == (-6, 16, -36, 46, -18), "exact pivot vectors")
    new_label = residue(signed[18])
    require(label == (2, 0, 4, 6, 6) and new_label == (2, 0, 0, 6, 2), "the pivot changes its indexed mod8 label")
    require(low_high_moments(upper_dots) == low_high_moments(list(signed.values())), "absolute mixed-bit moments")

    used_upper = set(anchors.values())
    remaining_above = [row for i, row in high.items() if i not in used_upper]
    remaining_below = [row for i, row in signed.items() if i not in anchors]
    counts = []
    for modulus in (8, 16, 32, 64, None):
        key = tuple if modulus is None else lambda row: residue(row, modulus)
        counts.append(len(anchors) + sum((Counter(map(key, remaining_above)) & Counter(map(key, remaining_below))).values()))
    special = sum(residue(row, 16) == (6, 4, 12, 14, 14) for row in signed.values())
    require(counts == [1193, 906, 282, 26, 15] and special == 3, "all four named pairs extend to a complete modulo-eight pairing")
    print(f"n=2396 exact reindexed pivot: four exact Sylvester pairs including 18/618; joint matches {tuple(counts)}; "
          f"second fold unchanged, {reindexed} indexed mod8 changes, special count {special}")


def main():
    here = Path(__file__).parent
    profiles = json.loads((here / "exterior_reindexed_anchors.json").read_text())
    upper = decode(json.loads((here / "exterior_mod16_invariant_witness.json").read_text())["upper"])
    top, lower, _, margins = gram_fixture()
    half = BOTTOM // 2
    require(INDEX < half and INDEX not in LOWER_OMISSIONS, "retained plus-copy pivot index")
    rows = [int(v, 32) for v in profiles["nine"]["lower"]]
    fixed = fold(rows)
    require(fixed == fold([int(v, 32) for v in profiles["eight"]["lower"]]), "eight and nine share the same fold")
    require([v.bit_count() for v in rows] == [v.bit_count() for v in margins], "exact physical row weights")
    lower_columns = decode(profiles["nine"]["lower"])
    require(all(a.bit_count() + b.bit_count() == ORDER // 2
                for a, b in zip(upper, lower_columns, strict=True)), "fixed global weights")
    dots = [-v for v in correlations([lower[INDEX]], lower_columns, BOTTOM)[0]]
    label = residue(dots)
    same_reference = residue(correlations([lower[INDEX]], decode(profiles["eight"]["lower"]), BOTTOM)[0])
    require(tuple((-v) % 8 for v in same_reference) == label == (2, 0, 4, 6, 6) and dots[SECOND] == -56,
            "unchanged reindexed label at the pivot")
    upper_dots = correlations(top[3:], upper, TOP)
    old_class = [v[SECOND] for v in upper_dots if residue(v) == label]
    fixed_capacity = plus_capacity(rows, fixed, INDEX, SECOND, released=0)
    second_capacity = plus_capacity(rows, fixed, INDEX, SECOND, released=((1 << WIDTH) - 1) ^ (1 << SECOND))
    require((fixed_capacity, second_capacity, len(old_class), min(old_class)) == (-48, -40, 63, -32),
            "both exact capacities exclude all partners with the old label")
    changed_labels = Counter(residue(v) for v in upper_dots if v[SECOND] % 8 == label[SECOND] and v[SECOND] <= second_capacity)
    require(changed_labels == {
        (2, 0, 0, 2, 6): 5, (2, 0, 0, 6, 2): 3, (2, 0, 4, 2, 2): 4, (6, 0, 0, 2, 2): 3,
        (6, 0, 0, 6, 6): 1, (6, 0, 4, 2, 6): 5, (6, 0, 4, 6, 2): 7,
    }, "all possible replacement labels after drifting")
    baseline, changes = priced_fold_changes(rows, INDEX, SECOND, price=-2)
    require(baseline == second_capacity and Counter(changes) == {-4: 128, 0: 300, 4: 172},
            "exact signed capacity changes at each candidate fold position")
    require(min(old_class) - baseline == 8, "two more favorable than unfavorable changed positions are necessary")
    print(f"n=2396 reindexed anchor pivot: index {INDEX}, global-weight caps {fixed_capacity}/{second_capacity}, "
          f"same-label upper minimum {min(old_class)}; {len(changed_labels)} labels across {sum(changed_labels.values())} upper indices")
    print("n=2396 pivot fold move: at least two more changes in 172 favorable than 128 unfavorable positions")
    check_witness(here, profiles["nine"]["lower"], profiles["nine"]["anchors"], upper, top, lower, upper_dots, label)


if __name__ == "__main__":
    main()
