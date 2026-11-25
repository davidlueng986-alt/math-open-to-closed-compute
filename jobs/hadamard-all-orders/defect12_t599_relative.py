"""Exact relative-support lift for the two fixed-comparator autocorrelations."""

from collections import Counter, defaultdict
from itertools import combinations

from defect12_t599_near64 import ALL, rotate, source_words


INITIAL, Q_COMPARATOR, TAU = source_words()
INTERIOR = (1 << 149) - 2
WHOLE = (1 << 149) - 1
ANTI_ORBITS = tuple((1 << i) | (1 << (149 - i)) for i in range(1, 75))
SYMMETRIC_ORBITS = tuple((1 << i) | (1 << (148 - i)) for i in range(75))
SELECTORS = [(word, 0) for word in ANTI_ORBITS] + [(0, word) for word in SYMMETRIC_ORBITS]
LAGS = range(296, 1, -2)
ELIGIBLE = [ALL ^ ((Q_COMPARATOR ^ rotate(Q_COMPARATOR, d)) | (TAU ^ rotate(TAU, d)))
            for d in LAGS]


def bit_indices(word):
    while word:
        low = word & -word
        yield low.bit_length() - 1
        word ^= low


def initial_supports():
    # P contains even positions of A; S contains odd positions of B.
    # Q contains odd positions of A; R contains even positions of B.
    initial_u = sum(1 << j for j in range(1, 149)
                    if (INITIAL >> (2 * j) & 1) == (INITIAL >> (300 + 2 * j) & 1))
    initial_t = sum(1 << j for j in range(149)
                    if (INITIAL >> (2 * j + 1) & 1) == (INITIAL >> (301 + 2 * j) & 1))
    return initial_u, initial_t


def packed_square_sum(word, universe):
    # Each coefficient is below 1024, so these integer products encode
    # coefficientwise square sums without inter-coefficient carries.
    def packed(mask):
        return sum(1 << (10 * j) for j in bit_indices(mask))

    return packed(word)**2 + packed(universe ^ word)**2


def low_coefficients(u_mask, t_mask):
    left = packed_square_sum(u_mask, INTERIOR)
    right = packed_square_sum(t_mask, WHOLE)
    return tuple((((right >> (10 * (d - 1))) & 3) - ((left >> (10 * d)) & 3)) % 4
                 for d in range(1, 149))


def relative_syndrome(u_mask, t_mask):
    coefficients = low_coefficients(u_mask, t_mask)
    assert all(value % 2 for value in coefficients)
    return sum((((coefficients[j] + coefficients[147 - j]) % 4) // 2) << j for j in range(74))


def compose_word(u_mask, t_mask, orientations=0):
    low = low_coefficients(u_mask, t_mask)
    assert all((low[j] + low[147 - j]) % 4 == 0 for j in range(74))
    p = [1, *(1 if value == 1 else -1 for value in low), -1]
    s = [p[j] if u_mask >> j & 1 else -p[j] for j in range(1, 149)]
    reference = [1 - 2 * (INITIAL >> (2 * j + 1) & 1) for j in range(149)]
    q = [sign * (1 - 2 * (orientations >> min(j, 148 - j) & 1)) for j, sign in enumerate(reference)]
    r = [q[j] if t_mask >> j & 1 else -q[j] for j in range(149)]
    word = INITIAL & ((1 << 299) | (1 << 300) | (1 << 598))
    for factor, first in ((p, 0), (q, 1), (r, 301), (s, 302)):
        word |= sum((sign < 0) << (first + 2 * j) for j, sign in enumerate(factor))
    return word


def autocorrelations(word):
    return [mask.bit_count() - 2 * ((word ^ rotate(word, d)) & mask).bit_count()
            for d, mask in zip(LAGS, ELIGIBLE, strict=True)]


def eliminate_columns(columns):
    pivots = {}
    for j, column in enumerate(columns):
        choices = 1 << j
        while column:
            i = column.bit_length() - 1
            if i not in pivots:
                pivots[i] = (column, choices)
                break
            previous, expression = pivots[i]
            column ^= previous
            choices ^= expression
    return pivots


def check_high_lift(u_mask, t_mask):
    start = autocorrelations(compose_word(u_mask, t_mask))
    assert all(value % 8 == 0 for value in start)
    residual = sum((value // 8 % 2) << j for j, value in enumerate(start))
    columns = []
    for j, orbit in enumerate(SYMMETRIC_ORBITS):
        support = t_mask if t_mask >> j & 1 else WHOLE ^ t_mask
        square = sum(1 << (2 * i) for i in bit_indices(orbit))
        product = 0
        for i in bit_indices(orbit):
            product ^= support << i
        columns.append((product ^ square) & ((1 << 148) - 1))
    pivots = eliminate_columns(columns)
    orientations = 0
    for i, (column, expression) in sorted(pivots.items(), reverse=True):
        if residual >> i & 1:
            residual ^= column
            orientations ^= expression
    replay = autocorrelations(compose_word(u_mask, t_mask, orientations))
    assert sum((value // 8 % 2) << j for j, value in enumerate(replay)) == residual
    return residual, len(pivots)


def verify():
    u0, t0 = initial_supports()
    target = relative_syndrome(u0, t0)
    assert target == 1 << 72
    columns = [target ^ relative_syndrome(u0 ^ u, t0 ^ t) for u, t in SELECTORS]
    assert len(columns) == 149 and len(eliminate_columns(columns)) == 74

    by_syndrome = defaultdict(list)
    by_syndrome[0].append(0)
    for size in (1, 2, 3):
        for indices in combinations(range(len(columns)), size):
            image = 0
            for j in indices:
                image ^= columns[j]
            by_syndrome[image].append(sum(1 << j for j in indices))
    candidates = {left ^ right for image, left_words in by_syndrome.items()
                  for left in left_words for right in by_syndrome.get(image ^ target, ())}
    assert Counter(word.bit_count() for word in candidates) == {1: 1, 2: 2, 3: 2, 4: 74, 5: 216, 6: 354}
    for choice in candidates:
        u_mask, t_mask = u0, t0
        for j in bit_indices(choice):
            u, t = SELECTORS[j]
            u_mask ^= u
            t_mask ^= t
        assert relative_syndrome(u_mask, t_mask) == 0
        residual, rank = check_high_lift(u_mask, t_mask)
        assert rank == 73 and residual

    assert pow(2, 74, 149) == 148 and pow(2, 4, 149) != 1
    print("t=599: relative support rank 74 on 149 selectors; 649 supports within six changes reach mod32")
    print("t=599: none of these 649 supports attains mod64 under any of its 2^75 orientations")


if __name__ == "__main__":
    verify()
