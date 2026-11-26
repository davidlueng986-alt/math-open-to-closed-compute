"""Replay the complete shared-change screen with two independent centers."""

from collections import Counter
from itertools import combinations

from border4_2396 import periodic
from border4_2396_dual_quotient import (
    CHANGED_C13_MARGINS, LOW_AMPLITUDE_MOD16, MASKS, MORE_MOD16, dual_words,
)

N = 299
DISTANCES = range(1, 150)


def eligible(row):
    result = []
    for center in range(N):
        masks = [0, 0]
        for distance in DISTANCES:
            value = row[(center+distance) % N]
            if value and value == -row[(center-distance) % N]:
                masks[value > 0] |= 1 << distance
        result.append(tuple(masks))
    return result


def margin_column(distance):
    column = 0
    for modulus, offset in ((13, 0), (23, 6)):
        coordinate = distance % modulus
        if coordinate:
            index = min(coordinate, modulus-coordinate)
            sign = 1 if coordinate == index else -1
            column += sign << (6*(offset+index-1))
    return column


MARGINS = tuple(map(margin_column, range(150)))


def balanced(options):
    # Each signed digit is in [-31,31], so the packed sum is zero iff
    # all the integer quotient sums are zero.
    assert len(options) <= 31
    values = [sign * MARGINS[distance] for distance, sign in options]
    total = selected = 0
    for step in range(1, 1 << len(options)):
        bit = step & -step
        selected ^= bit
        value = values[bit.bit_length()-1]
        total += value if selected & bit else -value
        if total == 0:
            yield tuple(option for i, option in enumerate(options) if selected >> i & 1)


def shifted_delta(center, sign, changes):
    delta = {}
    for distance, value in changes:
        delta[(center+distance) % N] = sign*value
        delta[(center-distance) % N] = -sign*value
    return delta


def correlation_change(row, delta, lag):
    return 2*sum(value*(row[(i+lag) % N] + row[(i-lag) % N]
                        + 2*delta.get((i+lag) % N, 0))
                 for i, value in delta.items())


def screen(words):
    populations = tuple(map(eligible, words))
    raw = periodic(words)
    # Reject the baseline and try its failing lags first for every change.
    lags = sorted(DISTANCES, key=lambda d: (raw[d]+2) % 11 == 0)
    assert (raw[lags[0]]+2) % 11
    settings = physical_subsets = 0
    balanced_by_size = Counter()
    for i, j in combinations(range(4), 2):
        for first, (an, ap) in enumerate(populations[i]):
            for second, (bn, bp) in enumerate(populations[j]):
                for sign, positive, negative in ((1, ap & bp, an & bn), (-1, ap & bn, an & bp)):
                    settings += 1
                    union = positive | negative
                    physical_subsets += (1 << union.bit_count()) - 1
                    if union.bit_count() < 2:
                        continue
                    options = []
                    while union:
                        bit = union & -union
                        options.append((bit.bit_length()-1, -1 if bit & positive else 1))
                        union ^= bit
                    for changes in balanced(options):
                        balanced_by_size[len(changes)] += 1
                        a = shifted_delta(first, 1, changes)
                        b = shifted_delta(second, sign, changes)
                        assert any((raw[d]+2 + correlation_change(words[i], a, d)
                                    + correlation_change(words[j], b, d)) % 11 for d in lags)
    assert settings == 6 * 299**2 * 2
    return physical_subsets, sorted(balanced_by_size.items())


def main():
    sources = (
        (MASKS, 3857971, [(3, 71), (4, 138), (5, 2), (6, 6), (7, 1)]),
        (MORE_MOD16, 3407726, [(3, 110), (4, 141), (5, 4), (7, 1)]),
        (CHANGED_C13_MARGINS, 3441370, [(3, 113), (4, 164), (5, 5), (6, 6), (7, 1)]),
        (LOW_AMPLITUDE_MOD16, 3559572, [(3, 142), (4, 261), (5, 9), (6, 6), (7, 2), (8, 6), (10, 1)]),
    )
    for masks, subsets, balanced_counts in sources:
        assert screen(dual_words(masks)) == (subsets, balanced_counts)
    print("Four × 1,072,812 two-row settings at arbitrary shared-change axes. No mod-11 lift.")


if __name__ == "__main__":
    main()
