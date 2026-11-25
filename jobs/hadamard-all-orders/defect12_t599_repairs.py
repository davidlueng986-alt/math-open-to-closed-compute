"""Certify a repair-radius bound for the fixed comparator at length 599."""

from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations

from defect12_t599_near64 import ALL, LENGTH, rotate, source_words


LONG_HALF = 149
SHORT_HALF = 148
SYNDROME_SIZE = 148
QUICK_GROUPS = 12
EXTENDED_GROUPS = 18
EXPECTED_COUNTS = (0,) * 9 + (2, 3, 1, 4, 2, 2, 6, 14, 12, 46)


def mirrored_columns():
    """Collect equal mod-8 columns after taking a binary finite difference."""
    raw = [0] * (LONG_HALF + SHORT_HALF + 2)
    for half, offset in ((LONG_HALF, 0), (SHORT_HALF, LONG_HALF + 1)):
        for coordinate, distance in enumerate(range(2, 2 * LONG_HALF, 2)):
            for i in range(2 * half + 1 - distance):
                j = i + distance
                # Count one of each pair of reflected edges. A fixed edge
                # has the same flip at both ends and contributes no change.
                if i + j < 2 * half:
                    raw[offset + min(i, 2 * half - i)] ^= 1 << coordinate
                    raw[offset + min(j, 2 * half - j)] ^= 1 << coordinate
    groups = defaultdict(list)
    for variable, column in enumerate(raw):
        groups[column ^ (column << 1)].append(variable)
    columns = list(groups)
    variables = list(groups.values())
    pairs = {tuple(v) for v in variables if len(v) > 1}
    assert pairs == {(2 * j + 1, LONG_HALF + 1 + 2 * j) for j in range(75)}
    assert len(columns) == 224 and all(c.bit_count() in (2, 4) for c in columns)
    return columns, variables


def mirrored_signs(variable):
    if variable <= LONG_HALF:
        return (1 << variable) | (1 << (2 * LONG_HALF - variable))
    index = variable - LONG_HALF - 1
    return (1 << (301 + index)) | (1 << (597 - index))


def syndrome_supports(columns, target, maximum):
    """Enumerate every distinct-column support of the prescribed syndrome."""
    incidence = [sum(1 << i for i, column in enumerate(columns) if (column >> j) & 1)
                 for j in range(SYNDROME_SIZE + 1)]
    assert max(options.bit_count() for options in incidence) == 6
    one_column = {c: i for i, c in enumerate(columns)}
    two_columns = defaultdict(list)
    for i, j in combinations(range(len(columns)), 2):
        two_columns[columns[i] ^ columns[j]].append((1 << i) | (1 << j))

    def visit(syndrome, size, available, support):
        if syndrome.bit_count() > 4 * size:
            return
        if size == 0:
            if syndrome == 0:
                yield support
            return
        if size == 1:
            i = one_column.get(syndrome)
            if i is not None and (available >> i) & 1:
                yield support | (1 << i)
            return
        if size == 2:
            for pair in two_columns.get(syndrome, ()):
                if pair & available == pair:
                    yield support | pair
            return

        candidates = available
        if syndrome:
            uncovered = syndrome
            disjoint_options = 0
            lower_bound = 0
            shortest = len(columns) + 1
            while uncovered:
                bit = uncovered & -uncovered
                uncovered ^= bit
                options = incidence[bit.bit_length() - 1] & available
                if not options:
                    return
                if not (options & disjoint_options):
                    disjoint_options |= options
                    lower_bound += 1
                    if lower_bound > size:
                        return
                if options.bit_count() < shortest:
                    candidates = options
                    shortest = options.bit_count()

        # If the syndrome is nonzero, every remaining support has a least
        # member in the chosen incidence set. At zero, branch instead on
        # its least available member, admitting additional kernel moves.
        while candidates:
            bit = candidates & -candidates
            candidates ^= bit
            available ^= bit
            i = bit.bit_length() - 1
            yield from visit(syndrome ^ columns[i], size - 1, available, support | bit)

    available = (1 << len(columns)) - 1
    for size in range(maximum + 1):
        yield size, visit(target, size, available, 0)


def reduce_binary(pivots, word):
    while word:
        leader = word.bit_length() - 1
        if leader not in pivots:
            break
        word ^= pivots[leader]
    return word


def verify(maximum=QUICK_GROUPS):
    assert LENGTH == 599
    assert all(149 % d for d in range(2, 13))
    assert pow(2, 148, 149) == 1 and pow(2, 74, 149) == 148 and pow(2, 4, 149) == 16
    seed, q, half = source_words()
    assert all(((seed >> i) ^ (seed >> (298 - i))) & 1 == (1 - i % 2) for i in range(299))
    assert all(((seed >> (301 + i)) ^ (seed >> (597 - i))) & 1 == i % 2 for i in range(297))
    assert ((seed >> 300) ^ (seed >> 598)) & 1 == 0
    masks = tuple((d, ALL ^ ((rotate(q, d) ^ q) | (rotate(half, d) ^ half)))
                  for d in range(2, 2 * LONG_HALF, 2))

    def correlations_over_four(signs):
        return [mask.bit_count() - 2 * ((signs ^ rotate(signs, d)) & mask).bit_count()
                for d, mask in masks]

    def residual(signs):
        coefficients = correlations_over_four(signs)
        assert all(value % 8 == 0 for value in coefficients)
        return sum(((value // 8) & 1) << j for j, value in enumerate(coefficients))

    initial = correlations_over_four(seed)
    assert all(value % 4 == 0 for value in initial)
    defect = sum(((value // 4) & 1) << j for j, value in enumerate(initial))
    assert defect == 1 << 75
    target = defect ^ (defect << 1)
    columns, variables = mirrored_columns()
    paired_moves = [mirrored_signs(group[0]) ^ mirrored_signs(group[1]) for group in variables if len(group) == 2]

    midpoint_group = next(i for i, group in enumerate(variables) if LONG_HALF in group)
    minimum_signs = LENGTH
    for size, supports in syndrome_supports(columns, target, maximum):
        count = 0
        for support in supports:
            count += 1
            minimum_signs = min(minimum_signs, 2 * size - ((support >> midpoint_group) & 1))
            signs = seed
            for i, group in enumerate(variables):
                if (support >> i) & 1:
                    signs ^= mirrored_signs(group[0])
            base = residual(signs)
            pivots = {}
            # The paired changes are linear on this mod-8 coset. This
            # eliminates every choice of simultaneous changes in all 75
            # duplicate groups, including groups outside this support.
            for move in paired_moves:
                word = reduce_binary(pivots, residual(signs ^ move) ^ base)
                if word:
                    pivots[word.bit_length() - 1] = word
            assert len(pivots) == 73 and reduce_binary(pivots, base) != 0
        assert count == EXPECTED_COUNTS[size]
    assert minimum_signs == 18
    total = sum(EXPECTED_COUNTS[:maximum + 1])
    print("t=599: minimum 9 column groups and 18 individual signs for the mod-8 repair")
    print(f"all {total} supports with at most {maximum} groups fail modulo 64 after 75 paired directions")
    print(f"the fixed comparator has no repair within {2 * maximum} individual signs")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--extended", action="store_true", help="check 18 rather than 12 column groups")
    options = parser.parse_args()
    verify(EXTENDED_GROUPS if options.extended else QUICK_GROUPS)
