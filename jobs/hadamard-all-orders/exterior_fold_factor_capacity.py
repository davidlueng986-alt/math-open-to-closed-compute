"""Check exact scalar capacities and fold-distance bounds for the eight projection factors."""

from collections import defaultdict
import json
from pathlib import Path

from exterior_mod16_invariant import decode, omitted_residue_census, possible_copy_offsets
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture
from verify import paley, rows_from_columns


def local_options(left_weight, right_weight, fold, column):
    """Possible negative bits for a column with both row weights and the fold fixed."""
    return sorted({
        (left >> column & 1, (left ^ fold) >> column & 1)
        for left in range(1 << WIDTH)
        if left.bit_count() == left_weight and (left ^ fold).bit_count() == right_weight
    })


def free_bits(weight):
    if weight == 0:
        return (0,)
    if weight == WIDTH:
        return (1,)
    return (0, 1)


def scalar_bounds(row_pairs, column, weight, scores, demand):
    half = BOTTOM // 2
    local = []
    baseline = fixed_weight = 0
    gains = []
    for r, (first, second) in enumerate(row_pairs):
        w0, w1 = first.bit_count(), second.bit_count()
        options = local_options(w0, w1, first ^ second, column)
        a, b = scores[r], scores[r + half]
        possibilities = [(x + y, (1 - 2 * x) * a + (1 - 2 * y) * b) for x, y in options]
        local.append((possibilities, a, b, w0, w1))
        sizes = {size for size, _ in possibilities}
        if len(sizes) == 1:
            fixed_weight += possibilities[0][0]
            baseline += max(score for _, score in possibilities)
        else:
            require(sizes == {0, 2} and len(possibilities) == 2, "same-sign flexible row pair")
            positive, negative = sorted(possibilities)
            baseline += positive[1]
            gains.append(negative[1] - positive[1])

    remaining = weight - fixed_weight
    require(remaining % 2 == 0 and 0 <= remaining // 2 <= len(gains), "valid remaining weight")
    selections = remaining // 2
    gains.sort(reverse=True)
    capacity = baseline + sum(gains[:selections])
    require(capacity < demand, "fixed-fold capacity separates the factor")

    # The marginal gain divided by its two extra negative entries gives an
    # integer weight price making the sorting bound additive across base pairs.
    require(all(gain % 2 == 0 for gain in gains), "integral price")
    price = gains[max(0, selections - 1)] // 2 if gains else 0
    priced_baseline = price * weight
    increases = []
    for possibilities, a, b, w0, w1 in local:
        fixed = max(score - price * size for size, score in possibilities)
        unrestricted = max((1 - 2 * x) * a + (1 - 2 * y) * b - price * (x + y)
                           for x in free_bits(w0) for y in free_bits(w1))
        require(unrestricted >= fixed, "free local score dominates fixed-fold score")
        priced_baseline += fixed
        increases.append(unrestricted - fixed)
    require(priced_baseline == capacity, "weight price attains the sorting capacity")

    total = capacity
    for radius, gain in enumerate(sorted(increases, reverse=True), 1):
        total += gain
        if total >= demand:
            return capacity, radius
    raise ValueError("recorded factor demand exceeds even the unrestricted fold relaxation")


def factor_low_masks(factor):
    # B is the signed matching projection divided by two.
    return tuple(sum((value >> 1 & 1) << j for j, value in enumerate(row)) for row in factor)


def bit_indices(word):
    while word:
        low = word & -word
        yield low.bit_length() - 1
        word ^= low


def reduce_signature(pivots, pivot_mask, projection, fold):
    while remaining := projection & pivot_mask:
        signature, image = pivots[remaining.bit_length() - 1]
        projection ^= signature
        fold ^= image
    return projection, fold


def check_palettes(original, omitted_patterns, paley_rows):
    """Check that at most two new mask types cannot change the fold."""
    half = BOTTOM // 2
    palette = defaultdict(set)
    for pattern, mask in zip(omitted_patterns, original, strict=True):
        palette[pattern].add(mask)

    def signature(row, change):
        base = row % half
        old = paley_rows[base] | ((row >= half) << half)
        projection = sum(old << ((half + 1) * j) for j in bit_indices(change))
        fold = sum(1 << (half * j + base) for j in bit_indices(change))
        return projection, fold

    pivots = {}
    pivot_mask = 0
    variables = 0
    for row, (mask, pattern) in enumerate(zip(original, omitted_patterns, strict=True)):
        for replacement in sorted(palette[pattern] - {mask}):
            projection, fold = reduce_signature(pivots, pivot_mask, *signature(row, mask ^ replacement))
            if projection:
                lead = projection.bit_length() - 1
                pivots[lead] = projection, fold
                pivot_mask |= 1 << lead
            else:
                require(fold == 0, "the indexed modulo-eight kernel from the palette has zero fold image")
            variables += 1

    outside_by_weight = [[mask for mask in range(1 << WIDTH) if mask.bit_count() == weight]
                         for weight in range(WIDTH + 1)]
    directions = [
        [reduce_signature(pivots, pivot_mask, *signature(row, 1 | (1 << j)))
         for j in range(1, WIDTH)] for row in range(half)
    ]
    copy_difference = []
    for j in range(1, WIDTH):
        projected = (1 << half) | (1 << (half + (half + 1) * j))
        copy_difference.append(reduce_signature(pivots, pivot_mask, projected, 0))
    cosets = defaultdict(list)
    outsiders = 0
    for row, (mask, pattern) in enumerate(zip(original, omitted_patterns, strict=True)):
        # Equal-weight mask changes are even, so the four directions e_0+e_j
        # generate every row change.
        images = directions[row % half]
        if row >= half:
            images = [(a ^ c, b ^ d) for (a, b), (c, d) in zip(images, copy_difference, strict=True)]
        for replacement in outside_by_weight[mask.bit_count()]:
            if replacement in palette[pattern]:
                continue
            outsiders += 1
            projection = fold = 0
            for j in bit_indices((mask ^ replacement) >> 1):
                image, difference = images[j]
                projection ^= image
                fold ^= difference
            if projection == 0:
                require(fold == 0, "a single outside-palette row cannot change the fold")
            else:
                matches = cosets[projection]
                require(all(row == previous or fold == change for previous, change in matches),
                        "two distinct outside-palette rows cannot change the fold")
                matches.append((row, fold))
    return variables - len(pivots), outsiders


def main():
    directory = Path(__file__).parent
    top, lower, _, _ = gram_fixture()
    archived = json.loads((directory / "exterior_mod16_invariant_witness.json").read_text())
    factors = json.loads((directory / "exterior_exact_factor_witnesses.json").read_text())
    table = json.loads((directory / "exterior_fold_factor_capacities.json").read_text())
    require(len(factors) == 8 and set(table) == {str(i) for i in range(1, 9)}, "all eight fold layouts")
    upper = decode(archived["upper"])
    half = BOTTOM // 2
    require(len({i % half for i in LOWER_OMISSIONS}) == len(LOWER_OMISSIONS),
            "each omitted index has a retained Sylvester partner")
    upper_dots = correlations(top[3:], upper, TOP)
    _, _, feasible_low_profiles = omitted_residue_census(top, upper)
    require(len(feasible_low_profiles) == 1, "unique unordered omitted low profile")
    masks = feasible_low_profiles[0][0]
    require(len(set(masks)) == len(LOWER_OMISSIONS) - 1
            and all(factor_low_masks(entry["factor"]) == masks for entry in factors),
            "distinct canonical low masks for each exact factor")
    lower_omitted = [lower[i] for i in LOWER_OMISSIONS[1:]]
    omitted_patterns = rows_from_columns(BOTTOM, [lower[i] for i in LOWER_OMISSIONS])
    paley_rows = rows_from_columns(half, paley(half - 1))
    weights = [ORDER // 2 - TOP + column.bit_count() for column in upper]
    constant = [TOP - 2 * column.bit_count() for column in upper]
    require(possible_copy_offsets(upper_dots, constant, masks) == [20], "unique Sylvester copy shift")

    checks = 0
    palette_census = []
    for i, entry in enumerate(factors, 1):
        original = [int(symbol, 32) for symbol in entry["lower"]]
        lower_signs = decode(entry["lower"])
        require([BOTTOM - column.bit_count() for column in lower_signs] == weights,
                "each exact lower negative count")
        require(correlations(lower_omitted, lower_signs, BOTTOM)
                == [[-2 * value for value in row] for row in entry["factor"]], "physical factor labels")
        require(sum(((column >> half).bit_count() % 2) << j
                    for j, column in enumerate(lower_signs)) == 20, "recorded copy shift")
        row_pairs = list(zip(original[:half], original[half:], strict=True))
        seen = set()
        radii = [0] * 8
        for dst, column, coefficients, demand, cap, radius in table[str(i)]:
            require(dst in range(1, 9) and dst != i and dst not in seen and column in range(WIDTH),
                    "one certificate for an alternative factor")
            seen.add(dst)
            scores = [sum(coeff * (2 * (old >> r & 1) - 1)
                          for coeff, old in zip(coefficients, lower_omitted, strict=True))
                      for r in range(BOTTOM)]
            factor = factors[dst - 1]["factor"]
            require(demand == sum(-2 * coeff * row[column]
                                  for coeff, row in zip(coefficients, factor, strict=True)),
                    "exact scalar target demand")
            require(scalar_bounds(row_pairs, column, weights[column], scores, demand) == (cap, radius),
                    "exact scalar capacity and changed-fold lower bound")
            radii[dst - 1] = radius
            checks += 1
        require(seen == set(range(1, 9)) - {i}, "every alternative factor separated")
        print(f"n=2396 fold {i}: all seven competing factors excluded at this fold; distance bounds {radii}")
        palette_census.append(check_palettes(original, omitted_patterns, paley_rows))
    require(checks == 56, "verified every directed capacity certificate")
    require(palette_census == [(16, 6635), (36, 6514), (0, 6564), (52, 6562),
                              (13, 6545), (103, 6490), (74, 6483), (54, 6514)],
            "palette kernel nullities and outside-palette alternatives")
    print("n=2396 all eight layouts: an indexed-preserving fold change needs at least three outside-palette rows")


if __name__ == "__main__":
    main()
