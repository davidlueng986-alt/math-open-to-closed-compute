"""Rebuild two five-column exterior fixtures and check exact obstructions."""

from collections import Counter
from itertools import combinations

from verify import (
    determinant,
    goethals_seidel,
    length_299_words,
    paley,
    require,
    rows_from_columns,
    verify_orthogonal,
)


TOP, BOTTOM, WIDTH = 1196, 1200, 5
ORDER = TOP + BOTTOM
LOWER_OMISSIONS = (0, 1, 40, 602, 978, 1013, 1108)
ORIGINAL_TYPES = (
    (1, 64, 0, 150, 0, 0, 220, 0, 181, 0, 0, 55, 0, 0, 172, 0,
     53, 0, 94, 71, 0, 0, 0, 0, 134, 1, 0, 0, 0, 0, 0, 0),
    (24, 123, 0, 0, 0, 17, 0, 0, 0, 0, 1, 0, 0, 189, 0, 1,
     0, 18, 1, 0, 206, 93, 0, 63, 0, 0, 110, 117, 0, 94, 1, 142),
)
SPECTRAL_TOP_TYPES = (
    (67, 72, 52, 66, 41),
    (0, 74, 55, 154, 0, 0, 0, 0, 16, 0),
    (0, 0, 0, 0, 142, 142, 1, 14, 0, 0),
    (0, 0, 0, 122, 0, 0, 0, 0, 0, 177),
)
SPECTRAL_BOTTOM_TYPES = (
    24, 48, 0, 0, 0, 0, 52, 67, 0, 0, 0, 124, 34, 42, 0, 0,
    75, 37, 79, 0, 10, 0, 34, 152, 31, 0, 67, 114, 58, 0, 10, 142,
)


def place_types(weights, counts):
    """Assign each negative mask to the last available row of its weight."""
    buckets = [[i for i, weight in enumerate(weights) if weight == k] for k in range(WIDTH + 1)]
    rows = [0] * len(weights)
    for pattern, count in enumerate(counts):
        bucket = buckets[pattern.bit_count()]
        require(0 <= count <= len(bucket), "row type fits its required weight")
        for _ in range(count):
            rows[bucket.pop()] = pattern
    require(not any(buckets), "all rows assigned")
    return rows


def upper_spectral_rows(top):
    rows = [0] * TOP
    for (c, d), counts in zip(((1, 1), (1, -1), (-1, 1), (-1, -1)),
                              SPECTRAL_TOP_TYPES, strict=True):
        indices = [i for i in range(1, TOP)
                   if (2 * (top[1] >> i & 1) - 1, 2 * (top[2] >> i & 1) - 1) == (c, d)]
        weight = (WIDTH - (1 + c + d)) // 2
        patterns = [sum(1 << j for j in positions) for positions in combinations(range(WIDTH), weight)]
        expanded = [pattern for pattern, count in zip(patterns, counts, strict=True) for _ in range(count)]
        for row, pattern in zip(indices, expanded, strict=True):
            rows[row] = pattern
    return rows


def positive_columns(negative_rows):
    return [sum((1 - (mask >> j & 1)) << i for i, mask in enumerate(negative_rows))
            for j in range(WIDTH)]


def correlations(left, right, length):
    return [[length - 2 * (a ^ b).bit_count() for b in right] for a in left]


def leading_minors(matrix):
    values = [determinant([row[:n] for row in matrix[:n]]) for n in range(1, len(matrix) + 1)]
    require(all(value.denominator == 1 for value in values), "integral determinants")
    return [int(value) for value in values]


def check_gram(top, new_top, spectral):
    gram = correlations(new_top, new_top, TOP)
    alpha = correlations(top[1:3], new_top, TOP)
    total = [a + b for a, b in zip(*alpha, strict=True)]
    base = [[ORDER * (BOTTOM * (i == j) - gram[i][j]) for j in range(WIDTH)] for i in range(WIDTH)]
    doubled = [[2 * base[i][j] + total[i] * total[j] for j in range(WIDTH)] for i in range(WIDTH)]
    minors = leading_minors(doubled)
    require(all(minors), "Jacobi inertia criterion has nonzero pivots")
    negative = sum(a * b < 0 for a, b in zip([1] + minors[:-1], minors, strict=True))
    require(negative == (1 if spectral else 2), "inertia of the doubled base Gram")
    print(f"  doubled base Gram leading minors {minors}; negative eigenvalues {negative}")
    if spectral:
        completed = [[base[i][j] + sum(row[i] * row[j] for row in alpha)
                      for j in range(WIDTH)] for i in range(WIDTH)]
        minors = leading_minors(completed)
        require(all(value > 0 for value in minors), "positive definite Gram after actual projections")
        require((minors[3] % 13, minors[4] % 169) == (5, 78), "local integral Gram obstruction")
        require(pow(5, 6, 13) == 12, "order-four minor is a nonsquare modulo 13")
        print("  actual projections give positive definite Gram; minor mod 13 = 5, determinant mod 169 = 78")


def check_pairing_residues(rho, spectral):
    low = [value % 4 for value in rho[0]]
    require(all(value % 4 == low[j] for row in rho for j, value in enumerate(row)), "common low residues")
    require(all(sum(row) == 2 for row in rho), "fixed retained row sum")
    masks = [sum((((value - low[j]) // 4) % 2) << j for j, value in enumerate(row)) for row in rho]
    histogram = Counter(masks)
    # Every complete Sylvester pair differs by a single common mask.
    costs = {0: sum(count % 2 for count in histogram.values())}
    for delta in range(1, 1 << WIDTH):
        if delta.bit_count() % 2 == 0:
            costs[delta] = sum(abs(histogram[mask] - histogram[mask ^ delta])
                               for mask in range(1 << WIDTH) if mask < mask ^ delta)
    if spectral:
        require(min(costs.values()) == 9, "nine leftovers exceed the seven singleton bases")
        print("  modulo 8: minimum of nine unmatched residues exceeds seven singleton bases")
    else:
        require(costs[0] == 7 and min(value for key, value in costs.items() if key) == 43,
                "only the zero pair difference survives the count")
        full = {mask: (count + 1) // 2 for mask, count in histogram.items()}
        require(sum(full.values()) == 600, "recovered full base row count")
        parity = [sum(count for mask, count in full.items() if mask >> j & 1) % 2 for j in range(WIDTH)]
        require(parity == [1, 1, 0, 1, 1], "incompatible with even Paley binary code")
        print(f"  modulo 8: only zero pair difference survives; full base column parities {parity}")


def check_fixture(top, lower, old, top_rows, bottom_rows, weights, spectral):
    require([mask.bit_count() for mask in top_rows + bottom_rows] == weights, "all prescribed row margins")
    new_top, new_bottom = positive_columns(top_rows), positive_columns(bottom_rows)
    new = [a | (b << TOP) for a, b in zip(new_top, new_bottom, strict=True)]
    require(all(col.bit_count() == ORDER // 2 for col in new), "balanced new columns")
    require(verify_orthogonal(ORDER, new) == 10, "all new columns mutually orthogonal")
    mixed = sum((a ^ b).bit_count() == ORDER // 2 for a in old for b in new)
    require(mixed == (266 if spectral else 277), "replay of the default pairing")
    print(f"{'positive-Gram' if spectral else 'original'} fixture: all margins, 10 new/new dots, {mixed}/5965 mixed zeros")
    check_gram(top, new_top, spectral)
    rho = correlations(top[3:], new_top, TOP)
    check_pairing_residues(rho, spectral)
    omitted_patterns = rows_from_columns(BOTTOM, [lower[j] for j in LOWER_OMISSIONS])
    require(omitted_patterns[1] == omitted_patterns[180], "same omitted pattern on two lower rows")
    retained_rows = rows_from_columns(BOTTOM, [col for j, col in enumerate(lower) if j not in LOWER_OMISSIONS])
    differences = [sum(2 * ((retained_rows[180] >> j & 1) - (retained_rows[1] >> j & 1)) * row[i]
                       for j, row in enumerate(rho)) for i in range(WIDTH)]
    expected = [1296, 248, -2184, 2416, -1776] if spectral else [-1360, -88, 1376, -896, 968]
    require(differences == expected and all(d not in (-2 * BOTTOM, 0, 2 * BOTTOM) for d in differences),
            "impossible sign differences for every column at the indexed pairing")
    print(f"  lower rows 1 and 180: impossible numerator differences {differences}")


def exterior_sources():
    """Build the normalized upper and lower source squares."""
    top = goethals_seidel(length_299_words())
    top_mask = (1 << TOP) - 1
    top = [col ^ (top_mask ^ top[0]) for col in top]
    top = [col if col & 1 else col ^ top_mask for col in top]
    paley_columns = paley(599)
    block_mask = (1 << 600) - 1
    require(all(row.bit_count() % 2 == 0 for row in rows_from_columns(600, paley_columns)),
            "the Paley negative rows also have even weight")
    copies = Counter(j % 600 for j in range(BOTTOM) if j not in LOWER_OMISSIONS)
    require(Counter(copies.values()) == {1: 7, 2: 593}, "Sylvester pair and singleton counts")
    positive_lower = ([col | (col << 600) for col in paley_columns]
                      + [col | ((col ^ block_mask) << 600) for col in paley_columns])
    lower = [col ^ ((1 << BOTTOM) - 1) for col in positive_lower]
    return top, lower


def main():
    top, lower = exterior_sources()
    retained_lower = [col for j, col in enumerate(lower) if j not in LOWER_OMISSIONS]
    old = [a | (b << TOP) for a, b in zip(top[3:], retained_lower, strict=True)]
    require(verify_orthogonal(ORDER, old) == 711028, "all old columns mutually orthogonal")
    weights = [WIDTH + sum(col >> i & 1 for col in old) - ORDER // 4 for i in range(ORDER)]
    weights[0], weights[TOP] = 0, WIDTH
    original_top = place_types(weights[:TOP], ORIGINAL_TYPES[0])
    original_bottom = place_types(weights[TOP:], ORIGINAL_TYPES[1])
    check_fixture(top, lower, old, original_top, original_bottom, weights, spectral=False)
    spectral_bottom = place_types(weights[TOP:], SPECTRAL_BOTTOM_TYPES)
    check_fixture(top, lower, old, upper_spectral_rows(top), spectral_bottom, weights, spectral=True)


if __name__ == '__main__':
    main()
