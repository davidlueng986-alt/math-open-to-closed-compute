"""Exact finite checks for the Paley split and 13-by-23 repeat exclusion."""

from itertools import combinations, combinations_with_replacement, permutations, product
from math import isqrt

from border4_2396 import periodic


def square_profiles(norm, count, odd=False):
    return [
        values for values in combinations_with_replacement(
            range(1 if odd else 0, isqrt(norm) + 1, 2 if odd else 1), count)
        if sum(value**2 for value in values) == norm
    ]


def verify_paley_split():
    def chi(x):
        return 0 if x % 599 == 0 else (1 if pow(x % 599, 299, 599) == 1 else -1)

    squares = [pow(49, j, 599) for j in range(299)]
    assert len(set(squares)) == 299 and all(chi(x) == 1 for x in squares)
    a = [chi(x - 1) for x in squares]
    b = [chi(-x - 1) for x in squares]
    assert a.count(0) == 1 and a[0] == 0 and all(a[j] == -a[-j] for j in range(299))
    assert sum(a) == 0 and abs(sum(b)) == 1
    expected = [597] + [-2] * 298
    assert periodic((a, b)) == expected
    for step in (1, 13, 23):
        compare = b[step:] + b[:step]
        positive = tuple((u + v) // 2 for u, v in zip(b, compare, strict=True))
        negative = tuple((u - v) // 2 for u, v in zip(b, compare, strict=True))
        assert all(u*u + v*v == 1 for u, v in zip(positive, negative, strict=True))
        assert periodic((a, positive, negative)) == expected


def verify_totals():
    assert square_profiles(13, 4) == [(0, 0, 2, 3), (1, 2, 2, 2)]
    assert square_profiles(23, 4) == [(1, 2, 3, 3)]
    assert square_profiles(52, 4, True) == [(1, 1, 1, 7), (1, 1, 5, 5), (3, 3, 3, 5)]
    assert square_profiles(92, 4, True) == [(1, 1, 3, 9), (3, 3, 5, 7)]

    repeated = []
    for same in range(1, isqrt(598) + 1, 2):
        pairs = square_profiles(1196 - 2*same**2, 2, True)
        repeated.extend((same, left, right) for left, right in pairs)
    assert repeated == [(7, 3, 33), (11, 15, 27), (15, 11, 25), (21, 5, 17)]
    assert all(same % 13 and same % 23 for same, _, _ in repeated)
    assert all(right - left > 2 for _, left, right in repeated)

    profiles = square_profiles(599, 4)
    unit = [values for values in profiles if values.count(1) == 1]
    assert unit == [(1, 6, 11, 21), (1, 7, 15, 18)]


def verify_no_triple_at_13():
    length = 13
    mask = (1 << length) - 1

    def correlation(word, d):
        rotated = ((word << d) & mask) | (word >> (length - d))
        return length - 2*(word ^ rotated).bit_count()

    spectra = {
        tuple(correlation(word, d) for d in range(1, 7))
        for word in range(1 << length)
        if word.bit_count() <= 6
    }
    assert len(spectra) == 187
    assert not any(tuple(-3 * v for v in spectrum) in spectra for spectrum in spectra)


def all_signed(profiles):
    for profile in profiles:
        for reorder in set(permutations(profile)):
            for signs in product((-1, 1), repeat=4):
                yield tuple(x*s for x, s in zip(reorder, signs, strict=True))


def quaternion_rows(alpha):
    a, b, c, d = alpha
    return ((a, -b, -c, -d), (b, a, -d, c), (c, d, a, -b), (d, -c, b, a))


def verify_coefficient_profiles():
    for alpha in all_signed(square_profiles(13, 4) + square_profiles(23, 4)):
        for a, b in combinations(quaternion_rows(alpha), 2):
            for sign in (-1, 1):
                weights = tuple(sorted(abs(x + sign*y) for x, y in zip(a, b) if x != -sign*y))
                assert len(weights) in (3, 4) or weights == (1, 5)


def verify_section_classes():
    patterns = {(0, 1, 2, 3)} | set(permutations((0, 0, 1, 2)))
    for length, classes, difference in product((13, 23), patterns, (1, 2, 3)):
        transition = tuple(tuple(v for v in range(4) if classes[u] == classes[v ^ difference])
                           for u in range(4))
        assert sum(u in transition[u] for u in range(4)) <= 2
        for first in range(4):
            states = {(first, 1 << first)}
            for _ in range(length):
                states = {(nxt, used | (1 << nxt))
                          for current, used in states for nxt in transition[current]}
            assert all(used.bit_count() <= 2 for last, used in states if last == first)


def main():
    verify_paley_split()
    verify_totals()
    verify_no_triple_at_13()
    verify_coefficient_profiles()
    verify_section_classes()
    print("Paley split exact. Both prime-factor quaternion families exclude repeated row classes.")
    print("All quaternion dependency patterns and required repeated-spectrum totals checked.")


if __name__ == "__main__":
    main()
