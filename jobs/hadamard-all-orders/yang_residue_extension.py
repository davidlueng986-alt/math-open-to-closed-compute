"""Check the modular certificate for the scalable Golay–Yang width family."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, lcm

from t187_yang import yang_selectors
from yang_four_residues import BASES

FIRST, STEP = 20_018_009, 24_342_780
BASE = 47
INITIAL, STEP_EXPONENT = 2, 239


def reduced_width(index, modulus):
    exponent = INITIAL + STEP_EXPONENT * index
    return BASE * (pow(16, exponent, modulus) + 1) % modulus


def check_primary_progression():
    modulus = 4 * STEP
    assert modulus == 16 * 3 * 5 * 7 * 11**2 * 479
    assert reduced_width(0, modulus) == 12_079
    assert (4 * FIRST * pow(12_079, -1, modulus) - 1) % modulus == 85_697_083
    for prime, period in ((3, 1), (5, 1), (7, 3), (11, 5), (479, 1)):
        assert pow(16, STEP_EXPONENT * period, prime) == 1
        for index in range(period):
            residue = reduced_width(index, prime)
            assert residue and (4 * FIRST - residue) % prime
    assert reduced_width(0, 2) == BASE % 2 == FIRST % 2 == 1 and modulus % 8 == 0


def forbidden_values(prime, period):
    assert prime not in (2, 47) and gcd(prime, 4 * STEP) == 1
    assert len({pow(16, STEP_EXPONENT*i, prime) for i in range(period)}) == period
    assert pow(16, STEP_EXPONENT*period, prime) == 1
    values = tuple(reduced_width(index, prime) for index in range(period))
    assert len(set(values)) == period and all(values)
    return tuple(value * pow(4, -1, prime) % prime for value in values)


def check_prescriptions():
    primes, periods = (13, 19, 23, 31), (3, 9, 11, 5)
    full_period = lcm(*periods)
    assert full_period == 495
    assert 1 not in forbidden_values(37, 9)
    assert (16*1+1) % 37 == 17 and all(i*i % 37 != 17 for i in range(37))

    masks = []
    for prime, period in zip(primes, periods, strict=True):
        values = forbidden_values(prime, period)
        forbidden = [0] * prime
        for index in range(full_period):
            forbidden[values[index % period]] |= 1 << index
        masks.append(forbidden)
    counts = Counter(full_period - (a | b | c | d).bit_count() for a,b,c,d in product(*masks))
    assert sum(counts.values()) == 176_111
    assert min(counts) == 200 and counts[200] == 990
    minimum = Fraction(min(counts), full_period)
    assert minimum == Fraction(40, 99)
    assert minimum-Fraction(2,5) == Fraction(2,495)
    print("scalable Yang AP: 176111 residue prescriptions; minimum 200 of 495 exponent classes")
    print("screened additional prime lists leave at least 2/495 of all exponent classes")


if __name__ == "__main__":
    base = BASES[799]
    assert tuple(map(len, base)) == (24, 24, 23, 23)
    assert len(yang_selectors(base)) == 799
    check_primary_progression()
    check_prescriptions()
