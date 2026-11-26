"""Replay coordinate-wise fold restrictions and an independent 148-fold witness."""

from collections import Counter
import json
from pathlib import Path

from exterior_fold_trade import omitted_residual
from exterior_mod16_invariant import decode, low_high_moments
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture
from verify import paley, rows_from_columns


HALF = BOTTOM // 2
FULL = (1 << WIDTH) - 1


def fold(rows):
    return [a ^ b for a, b in zip(rows[:HALF], rows[HALF:], strict=True)]


def residue(row, modulus=8):
    return tuple(v % modulus for v in row)


def row_options(rows, pattern, changed):
    masks = [tuple(s for s in range(FULL + 1) if s.bit_count() == count) for count in range(WIDTH + 1)]
    return [tuple((a, b) for a in masks[rows[r].bit_count()] for b in masks[rows[r + HALF].bit_count()]
                  if ((a ^ b ^ target) & ~changed) == 0)
            for r, target in enumerate(pattern)]


def price_mask(mask, omitted_pattern, terms):
    score = 0
    for index, price in terms:
        if index < WIDTH:
            score += price * (mask >> index & 1)
        else:
            row, column = divmod(index - WIDTH, WIDTH)
            score += price * (1 - 2 * (mask >> column & 1)) * (2 * (omitted_pattern >> row & 1) - 1)
    return score


def check_alternatives(cuts, reference, factors, lower):
    rows = [int(x, 32) for x in reference]
    omitted = [lower[i] for i in LOWER_OMISSIONS[1:]]
    omitted_patterns = rows_from_columns(BOTTOM, omitted)
    expected_residues = [residue(row) for row in correlations(omitted, decode(reference), BOTTOM)]
    require(len(set(expected_residues)) == len(omitted), "distinct omitted labels force indexed factor order")
    targets = [[tuple(-2*v for v in row) for row in rec["factor"]] for rec in factors]
    require(len(targets) == 8 and all([residue(row) for row in t] == expected_residues for t in targets),
            "the eight canonical factor orders")
    weights = [sum(row >> j & 1 for row in rows) for j in range(WIDTH)]
    actual_fold = fold(rows)
    expected_masks = sorted(FULL ^ (1 << j) for j in range(WIDTH))
    require(sorted(map(int, cuts)) == expected_masks, "all five choices of one fixed fold coordinate")
    count = 0
    min_gap = None
    for mask in expected_masks:
        checked = cuts[str(mask)]
        entries = list(range(1, 7 if mask == 29 else 8))
        require([row[0] for row in checked] == entries, "exact alternates excluded at this coordinate mask")
        options = row_options(rows, actual_fold, mask)
        grouped = Counter((omitted_patterns[r], omitted_patterns[r + HALF], row) for r, row in enumerate(options))
        for number, recorded_demand, recorded_capacity, terms in checked:
            target = weights + [x for row in targets[number - 1] for x in row]
            require(all(0 <= i < len(target) for i, _ in terms), "valid sparse price coordinates")
            demand = sum(target[i] * price for i, price in terms)
            cost = {pattern: [price_mask(x, pattern, terms) for x in range(FULL + 1)]
                    for pattern in set(omitted_patterns)}
            capacity = sum(n * max(cost[first][a] + cost[second][b] for a, b in options)
                           for (first, second, options), n in grouped.items())
            require((demand, capacity) == (recorded_demand, recorded_capacity) and capacity < demand,
                    "exact row-pair local maxima separate the alternate factor")
            min_gap = demand - capacity if min_gap is None else min(min_gap, demand - capacity)
            count += 1
    require(count == 34, "complete list of established separations")
    print(f"n=2396 fold-coordinate cuts: {count} exact separations; minimum gap {min_gap}; one four-coordinate case remains for factor 7")


def check_witness(lower_mask, expected, upper_string, reference, fixed, source):
    top, lower, upper_weights, lower_weights = source
    old_rows, closed_rows, rows = ([int(x, 32) for x in profile] for profile in (reference, fixed, lower_mask))
    require(len(rows) == BOTTOM and [x.bit_count() for x in rows] == [x.bit_count() for x in lower_weights],
            "exact physical lower row margins")
    require([int(x, 32).bit_count() for x in upper_string] == [x.bit_count() for x in upper_weights],
            "exact physical upper row margins")
    old, upper, new = [decode(profile) for profile in (reference, upper_string, lower_mask)]
    require(all((a.bit_count(), (a >> HALF).bit_count()) == (b.bit_count(), (b >> HALF).bit_count())
                for a, b in zip(old, new, strict=True)), "all half and global lower weights")
    require(all(a.bit_count() + b.bit_count() == ORDER // 2 for a, b in zip(upper, new, strict=True)), "exact outer weights")
    new_fold = fold(rows)
    changes = [a ^ b for a, b in zip(new_fold, fold(old_rows), strict=True)]
    require(set(changes) == {0, 17} and sum(bool(v) for v in changes) == 148, "new 148-row support in coordinates 1 and 5")
    require(sum(a != b for a, b in zip(new_fold, fold(closed_rows), strict=True)) == 248, "outside the former 136-fold branch")
    support = sum(1 << r for r, c in enumerate(changes) if c)
    require(all((support & col).bit_count() % 2 == 0 for col in paley(HALF - 1)), "actual fold delta is a Paley codeword")
    upper_gram, lower_gram = correlations(upper, upper, TOP), correlations(new, new, BOTTOM)
    require(all(upper_gram[i][j] + lower_gram[i][j] == ORDER * (i == j)
                for i in range(WIDTH) for j in range(WIDTH)), "complete outer new Gram")
    dots, old_dots = correlations(lower, new, BOTTOM), correlations(lower, old, BOTTOM)
    require(all(residue(a) == residue(b) for a, b in zip(dots, old_dots, strict=True)), "all 1200 indexed mod8 labels")
    beta = [dots[i] for i in LOWER_OMISSIONS]
    require(beta == [old_dots[i] for i in LOWER_OMISSIONS], "all 35 exact omitted projections")
    require(all(v == 0 for row in omitted_residual(correlations(top[1:3], upper, TOP), beta, upper_gram) for v in row),
            "all 25 exact omitted Gram entries")
    upper_dots = correlations(top[3:], upper, TOP)
    signed = [[-v for v in row] for i, row in enumerate(dots) if i not in LOWER_OMISSIONS]
    require(low_high_moments(upper_dots) == low_high_moments(signed), "absolute mixed-bit invariant")
    counts = [sum((Counter(residue(r, m) for r in upper_dots) & Counter(residue(r, m) for r in signed)).values())
              for m in (8,16,32,64)]
    counts.append(sum((Counter(map(tuple, upper_dots)) & Counter(map(tuple, signed))).values()))
    special = sum(residue(r, 16) == (6, 4, 12, 14, 14) for r in signed)
    require((counts, special) == expected, "joint projection overlaps and designated mod16 multiplicity")
    print(f"n=2396 indexed 148-fold witness: {counts[-1]} exact five-vectors, joint {tuple(counts)}, special count {special}")
    return rows, new_fold, upper_dots, dots


def plus_capacity(rows, fixed_fold, index, j, released):
    col = paley(HALF - 1)[index]
    paired = row_options(rows, fixed_fold, released)
    weight = sum(x >> j & 1 for x in rows)
    baseline = fixed_weight = 0
    gains = []
    for r, options in enumerate(paired):
        h = 2 * (col >> r & 1) - 1
        scores = {((a >> j & 1)+(b >> j & 1)): h*(2-2*((a >> j & 1)+(b >> j & 1))) for a, b in options}
        first = min(scores)
        baseline += scores[first]
        fixed_weight += first
        if len(scores) == 2:
            require(set(scores) == {0,2}, "a flexible equal-sign pair")
            gains.append(scores[2]-scores[0])
    rest = weight - fixed_weight
    require(rest % 2 == 0 and 0 <= rest // 2 <= len(gains), "feasible scalar total weight")
    return baseline + sum(sorted(gains, reverse=True)[:rest // 2])


def check_isolated_plus(rows, fixed_fold, upper_dots, dots):
    index, j = 313, 1
    require(index not in LOWER_OMISSIONS and index < HALF, "a retained plus-copy index")
    center = [-v for v in dots[index]]
    # Equal-sign pairs determine the plus-copy projection. Fixing their total negative count
    # fixes the residue in each unchanged fold coordinate, independently of the omitted dots.
    capacity = plus_capacity(rows, fixed_fold, index, j, released=0)
    maximum = center[j] + 8 * ((capacity - center[j]) // 8)
    eligible = [row[j] for row in upper_dots if residue(row) == residue(center)]
    require(len(eligible) == 74 and maximum < min(eligible), "the plus-copy index has no exact upper neighbor")
    print(f"n=2396 fixed 148-fold index {index}: plus capacity {maximum}, upper minimum {min(eligible)}, 74 candidates excluded")


def check_second_fold(reference, lower, upper_dots):
    index, column = 313, 1
    rows = [int(x, 32) for x in reference]
    require(index not in LOWER_OMISSIONS and index < HALF, "a retained plus-copy index")
    center = [-x for x in correlations([lower[index]], decode(reference), BOTTOM)[0]]
    label = residue(center)
    capacity = plus_capacity(rows, fold(rows), index, column, released=FULL ^ (1 << column))
    maximum = center[column] + 8 * ((capacity - center[column]) // 8)
    old_neighbors = [row[column] for row in upper_dots if residue(row) == label]
    require(label == (6, 0, 0, 6, 6) and maximum == -48 and len(old_neighbors) == 74
            and min(old_neighbors) == -40, "same label cannot be matched with only the second fold fixed")
    incoming = Counter(residue(row) for row in upper_dots if row[column] % 8 == label[column] and row[column] <= maximum)
    require(incoming == {
        (2, 0, 0, 2, 6): 3, (2, 0, 0, 6, 2): 1, (2, 0, 4, 2, 2): 2,
        (6, 0, 0, 2, 2): 1, (6, 0, 4, 2, 6): 2, (6, 0, 4, 6, 2): 2,
    }, "every viable replacement label and its exact multiplicity")
    print(f"n=2396 second-fold obstruction: index {index}, capacity {maximum}, "
          f"{len(incoming)} replacement mod8 labels across {sum(incoming.values())} upper indices")


def main():
    directory = Path(__file__).parent
    data = json.loads((directory / "exterior_fold_coordinates_certificate.json").read_text())
    factors = json.loads((directory / "exterior_exact_factor_witnesses.json").read_text())
    upper = json.loads((directory / "exterior_mod16_invariant_witness.json").read_text())["upper"]
    fixed = json.loads((directory / "exterior_fold_trade_exact_witness.json").read_text())["lower"]
    reference = factors[-1]["lower"]
    source = gram_fixture()
    check_alternatives(data["cuts"], reference, factors, source[1])
    exact = check_witness(data["lower_exact39"], ([1193,929,277,52,39], 6), upper, reference, fixed, source)
    special = check_witness(data["lower_special37"], ([1193,934,274,53,37], 3), upper, reference, fixed, source)
    require(exact[1] == special[1], "two witnesses in the same new physical fold")
    check_isolated_plus(*exact)
    check_second_fold(reference, source[1], exact[2])


if __name__ == "__main__":
    main()
