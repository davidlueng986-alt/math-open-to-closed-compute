"""Replay a five-column stack with exact row margins and omitted Gram equality."""

from collections import Counter

from five_column_constraints import (
    BOTTOM,
    LOWER_OMISSIONS,
    ORDER,
    TOP,
    WIDTH,
    correlations,
    exterior_sources,
    positive_columns,
    require,
    rows_from_columns,
)


# (Positive mask in omitted columns, negative mask in new columns, count).
UPPER_COUNTS = (
    (1, 13, 108), (1, 22, 15), (1, 28, 176),
    (3, 5, 75), (3, 9, 59), (3, 12, 1), (3, 17, 135), (3, 20, 29),
    (5, 3, 1), (5, 6, 138), (5, 10, 122), (5, 12, 29), (5, 17, 8), (5, 18, 1),
    (7, 1, 45), (7, 2, 73), (7, 4, 57), (7, 8, 54), (7, 16, 69),
)
HALF_BETA = (
    (67, 80, 122, 171, 159),
    (11, 254, 92, 99, 143),
    (181, 78, 270, 59, 11),
    (87, 102, 56, 265, 89),
    (87, 232, 102, 97, 81),
    (305, 72, 132, -51, 141),
)


LOWER_COUNTS = (
    (0, 31, 1), (2, 31, 25), (4, 31, 25), (6, 23, 24),
    (8, 31, 25), (10, 27, 12), (12, 23, 10), (12, 27, 10),
    (14, 19, 18), (16, 31, 26), (18, 15, 12), (18, 27, 6),
    (20, 23, 13), (20, 27, 1), (22, 11, 12), (22, 21, 5),
    (24, 27, 20), (26, 7, 9), (26, 22, 8), (28, 11, 10),
    (28, 25, 11), (30, 3, 15), (30, 6, 2), (32, 31, 20),
    (34, 27, 18), (36, 23, 1), (36, 27, 15), (38, 21, 21),
    (40, 29, 1), (40, 30, 17), (42, 7, 12), (42, 14, 2),
    (42, 25, 4), (42, 26, 5), (44, 13, 19), (46, 3, 9),
    (46, 5, 6), (48, 23, 20), (50, 14, 1), (50, 19, 15),
    (52, 21, 18), (54, 5, 20), (54, 20, 1), (56, 19, 13),
    (56, 22, 6), (56, 28, 1), (58, 18, 21), (60, 3, 1),
    (60, 17, 16), (62, 1, 17), (64, 31, 20), (66, 15, 17),
    (66, 27, 4), (68, 15, 17), (70, 11, 10), (70, 19, 7),
    (72, 30, 20), (74, 11, 16), (76, 26, 18), (78, 18, 20),
    (78, 20, 1), (80, 23, 11), (80, 30, 7), (82, 7, 9),
    (82, 22, 14), (84, 11, 7), (84, 22, 12), (86, 6, 3),
    (86, 12, 12), (88, 11, 12), (88, 22, 8), (90, 18, 18),
    (92, 3, 6), (92, 24, 10), (94, 1, 1), (94, 8, 7),
    (94, 16, 13), (96, 27, 19), (96, 30, 1), (98, 11, 17),
    (100, 7, 3), (100, 26, 3), (100, 28, 15), (102, 6, 8),
    (102, 9, 9), (104, 26, 26), (106, 24, 18), (108, 9, 11),
    (108, 17, 1), (108, 20, 2), (110, 8, 17), (112, 7, 25),
    (114, 6, 12), (116, 5, 1), (116, 24, 19), (118, 2, 2),
    (118, 8, 15), (118, 16, 1), (120, 12, 1), (122, 2, 1),
    (122, 16, 24), (124, 1, 8), (124, 2, 15), (124, 8, 2),
    (126, 0, 24),
)


def expand_profile(omitted_patterns, counts):
    groups = {pattern: [] for pattern in omitted_patterns}
    for omitted, negative, count in counts:
        require(count > 0 and omitted in groups, "valid grouped row count")
        groups[omitted].extend([negative] * count)
    require({pattern: len(group) for pattern, group in groups.items()}
            == Counter(omitted_patterns), "grouped counts fit omitted row patterns")
    return [groups[pattern].pop() for pattern in omitted_patterns]


def gram_fixture():
    """Return the normalized factors and five candidate sign rows for each half."""
    top, lower = exterior_sources()
    omitted_top = rows_from_columns(TOP, top[:3])
    omitted_lower = rows_from_columns(BOTTOM, [lower[j] for j in LOWER_OMISSIONS])
    top_rows = [0] + expand_profile(omitted_top[1:], UPPER_COUNTS)
    lower_rows = expand_profile(omitted_lower, LOWER_COUNTS)

    require(omitted_top[0] == 7 and all(mask.bit_count() == 4 - omitted.bit_count()
            for mask, omitted in zip(top_rows[1:], omitted_top[1:], strict=True)),
            "upper row margins")
    require(omitted_lower[0] == 0 and lower_rows[0] == 31 and all(
        mask.bit_count() == 6 - omitted.bit_count()
        for mask, omitted in zip(lower_rows[1:], omitted_lower[1:], strict=True)),
        "lower row margins")
    return top, lower, top_rows, lower_rows


def main():
    top, lower, top_rows, lower_rows = gram_fixture()
    new_top, new_lower = positive_columns(top_rows), positive_columns(lower_rows)
    require(all(a.bit_count() + b.bit_count() == ORDER // 2
                for a, b in zip(new_top, new_lower, strict=True)), "new columns balance")

    alpha = correlations(top[1:3], new_top, TOP)
    beta = correlations([lower[j] for j in LOWER_OMISSIONS[1:]], new_lower, BOTTOM)
    require(alpha == [[-394, 408, 608, 642, -66], [646, -640, 360, 278, 554]],
            "actual upper omitted projections")
    require(beta == [[2 * value for value in row] for row in HALF_BETA],
            "actual lower omitted projections")
    require(all(sum(row) == ORDER // 2 for row in alpha + beta), "omitted projection sums")

    gram = correlations(new_top, new_top, TOP)
    gram_lower = correlations(new_lower, new_lower, BOTTOM)
    require(all(gram[i][j] + gram_lower[i][j] == ORDER * (i == j)
                for i in range(WIDTH) for j in range(WIDTH)), "new columns are orthogonal")
    require(all(
        sum(row[i] * row[j] for row in beta) - sum(row[i] * row[j] for row in alpha)
        == ORDER * (BOTTOM * (i == j) - gram[i][j])
        for i in range(WIDTH) for j in range(WIDTH)), "all 25 omitted Gram entries")

    retained_lower = [column for j, column in enumerate(lower) if j not in LOWER_OMISSIONS]
    rho = correlations(top[3:], new_top, TOP)
    sigma = correlations(retained_lower, new_lower, BOTTOM)
    mixed = sum(x + y == 0 for a, b in zip(rho, sigma, strict=True)
                for x, y in zip(a, b, strict=True))
    require(mixed == 247, "indexed pairing mixed cancellation count")
    print("  five-column fixture: row and column balance, new/new orthogonality, omitted Gram equality")
    print(f"  indexed pairing cancels {mixed}/{len(rho) * WIDTH} mixed inner products")


if __name__ == "__main__":
    main()
