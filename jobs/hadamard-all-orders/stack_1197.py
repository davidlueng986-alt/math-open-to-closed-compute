"""Reconstruct and check 1197 mutually orthogonal sign columns at order 2396."""

from collections import defaultdict
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product
from math import isqrt

from verify import goethals_seidel, length_299_words, paley, verify_orthogonal


UPPER_FLIPS = (
    262, 1046, 819, 372, 333, 937, 475, 505, 546, 919, 344, 765, 578, 774, 1130,
    459, 799, 363, 649, 541, 1149, 1100, 164, 798, 1012, 328, 63, 886, 67, 703,
    283, 289,
)
LOWER_FLIPS = (
    93, 869, 881, 995, 790, 175, 801, 722, 726, 74, 840, 96, 538, 509, 1033, 701,
    248, 243, 84, 529, 799, 1089, 294, 480, 374, 876, 178, 989, 504, 1069, 650,
    293, 870, 390,
)
LOWER_OMITTED = (177, 573, 1123, 48)
COLUMN_HASH = "7010d9770a11bef6017d736b10f992b7e8756dd0bfa5d3f84b58ec37943c86da"


def normalize(columns):
    size = len(columns)
    mask = (1 << size) - 1
    return [mask ^ (column ^ columns[0]) for column in columns]


def flipped_column(size, flipped_rows):
    assert len(set(flipped_rows)) == len(flipped_rows)
    assert all(0 <= row < size for row in flipped_rows)
    return ((1 << size) - 1) ^ sum(1 << row for row in flipped_rows)


def correlations(columns, word):
    return [len(columns) - 2 * (column ^ word).bit_count() for column in columns]


def source_matrices():
    upper = goethals_seidel(length_299_words())
    paley_columns = paley(599)
    half_mask = (1 << 600) - 1
    lower = [column | (column << 600) for column in paley_columns]
    lower += [column | ((column ^ half_mask) << 600) for column in paley_columns]
    assert (len(upper), len(lower)) == (1196, 1200)
    return normalize(upper), normalize(lower)


def assemble(upper, lower, top_word, bottom_word, omitted):
    """Pair source columns by equal absolute projections, then append the new column."""
    top_size, bottom_size = len(upper), len(lower)
    top_dots = correlations(upper, top_word)
    bottom_dots = correlations(lower, bottom_word)
    assert sum(bottom_dots[j] ** 2 for j in omitted) == bottom_size**2 - top_size**2

    available = defaultdict(list)
    for j, dot in enumerate(bottom_dots):
        if j not in omitted:
            available[abs(dot)].append(j)

    columns = []
    lower_mask = (1 << bottom_size) - 1
    for upper_column, upper_dot in zip(upper, top_dots, strict=True):
        matches = available[abs(upper_dot)]
        assert matches
        j = matches.pop()
        lower_column = lower[j]
        if upper_dot + bottom_dots[j] != 0:
            assert upper_dot == bottom_dots[j]
            lower_column ^= lower_mask
        columns.append(upper_column | (lower_column << top_size))

    assert all(not matches for matches in available.values())
    columns.append(top_word | (bottom_word << top_size))
    return columns


def construct():
    upper, lower = source_matrices()
    top_word = flipped_column(len(upper), UPPER_FLIPS)
    bottom_word = flipped_column(len(lower), LOWER_FLIPS)
    top_dots = correlations(upper, top_word)
    bottom_dots = correlations(lower, bottom_word)
    assert top_dots[0] == bottom_dots[0] == 1132
    assert [abs(bottom_dots[j]) for j in LOWER_OMITTED] == [8, 36, 60, 68]
    return assemble(upper, lower, top_word, bottom_word, LOWER_OMITTED)


def check_extension_sieve():
    multiplier = 599
    threshold_partitions = []
    for radius in range(29):
        limit = radius + 2
        for values in combinations_with_replacement(range(limit % 2, limit + 1, 2), 4):
            if sum(value * value for value in values) == 4 * multiplier:
                threshold_partitions.append((radius, values))
    assert threshold_partitions == [(28, (6, 26, 28, 30)), (28, (12, 26, 26, 30)),
                                    (28, (14, 20, 30, 30))]

    _, lower = source_matrices()
    probes = correlations(lower, flipped_column(len(lower), LOWER_FLIPS))
    # Changing the sign of an omitted source column does not affect the Gram.
    first = tuple(abs(probes[j]) // 2 for j in LOWER_OMITTED)
    assert first == (4, 18, 30, 34)

    def dot(left, right):
        return sum(a * b for a, b in zip(left, right, strict=True))

    directions = [[], []]
    for parity, allowed in enumerate(((0, 4 * multiplier), (2 * multiplier,))):
        bound = isqrt(4 * multiplier)
        entries = [value for value in range(-bound, bound + 1) if value % 2 == parity]
        pairs = defaultdict(list)
        for a, b in product(entries, repeat=2):
            pairs[a*a + b*b].append((a, b))
        for squared, left in pairs.items():
            for ab, cd in product(left, pairs.get(4 * multiplier - squared, ())):
                candidate = ab + cd
                if next(value for value in candidate if value) > 0 and abs(dot(first, candidate)) in allowed:
                    directions[parity].append(candidate)
    even, odd = directions
    assert len(even) == 7 and len(odd) == 16

    def orthogonal(frame):
        return all(dot(a, b) == 0 for a, b in combinations(frame, 2))

    odd_frame_counts = []
    for rest in combinations((column for column in even if column != first), 3):
        frame = (first, *rest)
        if orthogonal(frame):
            compatible = [column for column in odd
                          if all(abs(dot(column, u)) == 2 * multiplier for u in frame)]
            odd_frame_counts.append(sum(orthogonal(group) for group in combinations(compatible, 4)))
    assert odd_frame_counts == [2, 2]
    print("n=2396 stacked extension: radius at least 28, 23 next projection directions, 4 full frame pairs")

    fixed = (0, 1, 600, 601)
    fixed_block = [tuple(2 * (lower[j] >> i & 1) - 1 for i in fixed) for j in fixed]
    normalized = {tuple(sorted(abs(dot(column, row_signs)) // 2 for column in fixed_block))
                  for row_signs in product((-1, 1), repeat=4)}
    assert normalized == {(1, 1, 1, 1), (0, 0, 0, 2)}
    partitions = [values for parity in (0, 1)
                  for values in combinations_with_replacement(range(parity, isqrt(4 * multiplier) + 1, 2), 4)
                  if dot(values, values) == 4 * multiplier]
    for order in (13, 23, 299):
        for values in partitions:
            folded = tuple(sorted(min(value % order, (-value) % order) for value in values))
            assert folded not in normalized
    print("n=2396 stacked extension: the matched 13-, 23-, and 299-fold projection families are impossible")


def verify():
    columns = construct()
    assert len(columns) == 1197
    assert verify_orthogonal(2396, columns) == 715806
    packed = "".join(f"{column:x}\n" for column in columns).encode("ascii")
    assert sha256(packed).hexdigest() == COLUMN_HASH
    print("n=2396: 1197 sign columns; all 715,806 pairwise inner products are zero")
    check_extension_sieve()


if __name__ == "__main__":
    verify()
