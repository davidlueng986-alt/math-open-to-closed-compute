"""Replay non-Williamson Ito controls and the prime-slice phase obstruction."""

from collections import Counter, defaultdict
from itertools import combinations, permutations, product
from math import comb, gcd

from paley_progression import verify_control
from t599_length_change import aperiodic, disjoint
from verify import rows_from_columns, signs, verify_orthogonal

ITO7 = ("+------", "+--+-++", "+---+-+", "++--+-+")
ITO11 = ("+--+++-++++", "+--++-+-+++", "+--+--+++++", "+-+++-+-+--")
WT_PROFILES = {
    ((4, 18_032), (12, 2_436), (20, 7)),
    ((4, 18_200), (12, 2_184), (20, 91)),
}


def negate(word):
    return tuple(-value for value in word)


def reverse(word):
    return word[:1] + word[:0:-1]


def frame(words):
    a, b, c, d = words
    return ((a, b, c, d), (b, negate(a), d, negate(c)),
            (c, negate(d), negate(a), b), (d, c, negate(b), negate(a)))


def ito_frame(words):
    rows = frame(words)
    return rows[:2] + tuple(tuple(reverse(word) for word in row) for row in rows[2:])


def columns(blocks):
    p = len(blocks[0][0])
    order = 4*p
    return [sum(1 << row for row in range(order)
                if blocks[row//p][col//p][(col - row) % p] == 1)
            for col in range(order)]


def row_product_profile(matrix_columns):
    order = len(matrix_columns)
    rows = rows_from_columns(order, matrix_columns)
    counts = Counter(abs(order - 2*(a ^ b ^ c ^ d).bit_count())
                     for a, b, c, d in combinations(rows, 4))
    return tuple(sorted(counts.items()))


def corr(left, right, offset):
    size = len(left)
    return sum(value * right[(index + offset) % size] for index, value in enumerate(left))


def pair_profile(left, right):
    offsets = range(1, 1 + len(left)//2)
    energy = tuple(corr(left, left, offset) + corr(right, right, offset) for offset in offsets)
    skew = tuple(corr(left, right, offset) - corr(right, left, offset) for offset in offsets)
    return energy, skew


def quaternary_word(left, right):
    return tuple(((a + b)//2, (b - a)//2) for a, b in zip(left, right, strict=True))


def verify_ito(words, expected_phase_counts):
    p = len(words[0])
    first, skew = pair_profile(*words[:2])
    second, opposite = pair_profile(*words[2:])
    assert first == negate(second) and skew == negate(opposite) and any(skew)
    quaternary = (quaternary_word(*words[:2]), quaternary_word(*words[2:]))
    assert tuple(sum(b != 0 for a, b in word) for word in quaternary) == expected_phase_counts
    for offset in range(p):
        real, imag = 0, 0
        for word in quaternary:
            for index, (a, b) in enumerate(word):
                c, d = word[(index + offset) % p]
                real += a*c + b*d
                imag += b*c - a*d
        assert (real, imag) == (2*p if offset == 0 else 0, 0)
    blocks = ito_frame(words)
    result = columns(blocks)
    assert verify_orthogonal(4*p, result) == comb(4*p, 2)
    return blocks, result


def williamson_census():
    p = 7
    words = [(1,) + word for word in product((-1, 1), repeat=p - 1)]
    zero = (0,)*(p//2)
    amicable = {}
    by_energy = defaultdict(list)
    for i in range(len(words)):
        for j in range(i, len(words)):
            energy, skew = pair_profile(words[i], words[j])
            amicable[i, j] = (skew == zero)
            if skew == zero:
                by_energy[energy].append((i, j))
    count, profiles = 0, set()
    for energy, first in by_energy.items():
        second = by_energy.get(negate(energy), ())
        for (i, j), (k, l) in product(first, second):
            if j > k or not all(amicable[u, v] for u, v in ((i, k), (i, l), (j, k), (j, l))):
                continue
            count += 1
            for a, b, c, d in set(permutations(words[index] for index in (i, j, k, l))):
                for first_word in (a, negate(a)):
                    profiles.add(row_product_profile(columns(frame((first_word, b, c, d)))))
    assert count == 28 and profiles == WT_PROFILES
    return profiles


def t11_selectors():
    base = tuple(map(signs, ("+++-++", "+++-+-", "+++--", "+-++-")))
    assert aperiodic(base) == [22] + [0]*5
    words = tuple(word + (0,)*5 for word in disjoint(*base[:2])) + tuple(
        (0,)*6 + word for word in disjoint(*base[2:]))
    assert aperiodic(words) == [11] + [0]*10
    result = []
    for position in zip(*words, strict=True):
        assert sum(map(abs, position)) == 1
        result.append(sum((i + 1)*value for i, value in enumerate(position)))
    return result


def verify_controls():
    blocks, h28 = verify_ito(tuple(map(signs, ITO7)), (3, 1))
    profile = row_product_profile(h28)
    assert profile == ((4, 18_018), (12, 2_457)) and profile not in williamson_census()
    assert verify_control(t11_selectors(), blocks) == 47_278
    print("Ito H(28) differs from every circulant Williamson template; lifted to H(308)")

    _, h44 = verify_ito(tuple(map(signs, ITO11)), (3, 5))
    assert len(h44) == 44 and all(x*x + y*y != 21 for x,y in product(range(5), repeat=2))
    print("Ito H(44): quaternary phase counts 3 and 5, with 21 not a sum of two squares")


def verify_slice():
    p, modulus = 261_129_632_466_031_099, 421_540_282_968_184_380
    assert p % 8 == 3 and (2*p - 1) % (31**2) == 31
    assert modulus % (31**2) == 0 and modulus % 8 == 4 and gcd(p, 2*modulus) == 1
    assert p % 3 == 1 and p % 5 == 4 and modulus % 15 == 0
    assert (4*p - 1) % 15 == 0
    print("Ito phase cut: p = 3 mod 8 and 31 exactly divides 2p-1 on the refined prime AP")


if __name__ == "__main__":
    verify_controls()
    verify_slice()
