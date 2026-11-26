"""Certify Golay–Paley compatible exponents and check a full H(1060) control."""

from math import gcd

from paley_progression import small_paley_blocks, verify_control
from t599_length_change import GOLAY_26, aperiodic

MODULUS = 24_342_780
TARGET = 20_018_009


def powers(base, modulus):
    result = {}
    value = 1
    while value not in result:
        result[value] = len(result)
        value = value * base % modulus
    assert value == 1
    return result


def verify_exponent_classes():
    odd_modulus = MODULUS // 4
    period_2 = powers(2, odd_modulus)
    assert len(period_2) == 157740 and 26 not in period_2
    assert pow(26, 2, odd_modulus) == pow(2, 29024, odd_modulus)
    q_modulus = 4 * MODULUS
    q_period = len(powers(3, q_modulus // 3))
    assert q_period == 14340
    assert gcd(TARGET, MODULUS) == 11 and pow(3, 5, 11) == 1
    inv_26 = pow(26, -1, odd_modulus)
    residue = 3
    eligible = 0
    classes = {}
    for exponent in range(1, q_period + 1):
        if exponent % 4 == 1:
            assert residue % 16 == 3
            side = (residue + 1) // 4
            if gcd(side, MODULUS) == 1:
                eligible += 1
                width = TARGET * pow(side, -1, MODULUS) % MODULUS
                assert width % 4 == 1
                assert width % 11 == 0 and width % 121 != 0
                length = (width - 1) // 2 % odd_modulus
                assert length not in period_2
                shifted = length * inv_26 % odd_modulus
                if shifted in period_2:
                    classes[exponent] = period_2[shifted]
        residue = residue * 3 % q_modulus
    assert residue == 3
    assert (eligible, len(classes)) == (2390, 595)
    assert classes[1] == 83022 and classes[2821] == 103482
    assert classes[28465 % q_period] == 102
    assert (6 + 9*29024) % len(period_2) == classes[2821]
    print("Golay–Paley conference-obstructed class: 595 of 14,340 exponent classes, all on the 26 coset")


def verify_progression():
    modulus = (4 * MODULUS // 11) * 13 * 19
    assert modulus == 2_186_424_240
    assert pow(3, 43020, modulus // 3) == 1
    for a, c, exponent, q, t19, discriminant in (
        (6, 19, 2821, 2_149_427_283, 15, 13),
        (102, 1, 28465, 937_023_363, 7, 18),
    ):
        width = 2 * 2**a * 26**c + 1
        assert width % 11 == 0 and pow(3, exponent, modulus) == q
        assert q % 8 == 3 and q % 3 == 0
        assert all(width * (modulus // 4) % m == 0 for m in (MODULUS, 13, 19))
        multiplier = width * ((q + 1) // 4)
        assert (multiplier % MODULUS, multiplier % 13, multiplier % 19) == (TARGET, 1, t19)
        assert multiplier % 121 == 11 and multiplier % 4 == 1
        assert (4*multiplier - 1) % (5*479) == (2*multiplier - 1) % (3*7) == 0
        assert (16*multiplier + 1) % 19 == discriminant
        assert discriminant not in {root*root % 19 for root in range(19)}
    first_width = 2 * 2**6 * 26**19 + 1
    assert gcd(1621, 2*13) == 1 and pow(3, 43020, 1621) == 1
    assert first_width * (pow(3, 2821, 1621) + 1) % 1621 == 4
    assert 7 not in {0, 3, 4, 9, 11, 13, 14, 15, 16}


def verify_seed():
    left, right = GOLAY_26
    assert aperiodic((left, right)) == [52] + [0]*25
    selectors = (*left, 2, *(3*value for value in right))
    assert verify_control(selectors, small_paley_blocks()) == 561270


if __name__ == "__main__":
    verify_exponent_classes()
    verify_progression()
    verify_seed()
