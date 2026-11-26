"""Exact seed and row-sum obstructions for one-step changes to length 599."""

from itertools import combinations_with_replacement, permutations, product
from math import isqrt

from verify import signs


GOLAY_26 = tuple(map(signs, ("++++-++--+-+-+--+-+++--+++", "++++-++--+-+++++-+---++---")))


def aperiodic(words):
    return [sum(a * b for word in words for a, b in zip(word, word[lag:]))
            for lag in range(max(map(len, words)))]


def disjoint(left, right):
    return (tuple((a + b) // 2 for a, b in zip(left, right, strict=True)),
            tuple((a - b) // 2 for a, b in zip(left, right, strict=True)))


def exact_t598():
    bases = tuple(map(signs, ("+-+--+++++++", "+-+++----++-", "+----+--++-", "++--+-+-+--")))
    assert aperiodic(bases) == [46] + [0] * 11
    first = disjoint(*bases[:2])
    second = disjoint(*bases[2:])
    base = tuple(word + (0,) * 11 for word in first) + tuple((0,) * 12 + word for word in second)
    assert aperiodic(base) == [23] + [0] * 22

    assert aperiodic(GOLAY_26) == [52] + [0] * 25
    x, y = disjoint(*GOLAY_26)
    words = []
    for left, right in (base[:2], base[2:]):
        words.append(tuple(a * c + b * d for a, b in zip(left, right, strict=True)
                           for c, d in zip(x, y[::-1], strict=True)))
        words.append(tuple(a * c - b * d for a, b in zip(left, right, strict=True)
                           for c, d in zip(y, x[::-1], strict=True)))
    assert all(sum(value * value for value in column) == 1 for column in zip(*words, strict=True))
    assert aperiodic(words) == [598] + [0] * 597
    assert tuple(map(sum, words)) == (18, -12, -11, 3)


def product_totals(base):
    """Both signs and all pairings of any of the input magnitudes are allowed."""
    totals = set()
    for order in set(permutations(base)):
        for orientation in product((-1, 1), repeat=4):
            a, b, c, d = (sign * value for sign, value in zip(orientation, order, strict=True))
            totals.add(tuple(sorted(map(abs, (a + 5*b, 5*a - b, c + 5*d, 5*c - d)))))
    return totals


def balanced_sign_sum(values):
    return any(sum(sign * value for sign, value in zip(pattern, values, strict=True)) == 0
               for pattern in product((-1, 1), repeat=4))


def verify():
    exact_t598()
    for residues in product(range(8), repeat=4):
        if sum(value * value for value in residues) % 8 == 0:
            assert all(value % 2 == 0 for value in residues)

    ternary = [p for p in combinations_with_replacement(range(isqrt(23) + 1), 4)
               if sum(value * value for value in p) == 23]
    binary = [p for p in combinations_with_replacement(range(1, isqrt(92) + 1, 2), 4)
              if sum(value * value for value in p) == 92]
    assert ternary == [(1, 2, 3, 3)]
    assert binary == [(1, 1, 3, 9), (3, 3, 5, 7)]
    golay_totals = [p for p in combinations_with_replacement(range(0, isqrt(52) + 1, 2), 2)
                    if sum(value * value for value in p) == 52]
    assert golay_totals == [(4, 6)]

    first_totals = product_totals(ternary[0])
    second_totals = set().union(*(product_totals(p) for p in binary))
    assert len(first_totals) == 6 and len(second_totals) == 12
    assert all(all(values) and not balanced_sign_sum(values) for values in first_totals)
    assert all(not balanced_sign_sum(values) for values in second_totals)
    print("t=599 length change: exact aperiodic T598 witness; no single insertions in either 23-by-26 product family")
    print("t=599 length change: the modulo-eight square obstruction rules out one deletion per word from length 600")


if __name__ == "__main__":
    verify()
