"""Replay the Golay classification in the conference-obstructed progression."""

from itertools import combinations
from math import comb, isqrt

from t599_length_change import GOLAY_26, aperiodic
from verify import goethals_seidel, rows_from_columns, verify_orthogonal

FIRST = 20_018_009
STEP = 24_342_780
ODD_MODULUS = STEP // 4
BASE_EXPONENT = 83_022
DIRECT_PERIOD = 157_740
DISJOINT_PERIOD = 473_220
TARGET = (FIRST - 1) // 2


def check_arithmetic():
    assert FIRST == 599 + 100_590 * 199 and STEP == 100_590 * 242
    assert STEP % 121 == 0 and FIRST % 121 == 11
    assert STEP % 4 == 0 and FIRST % 4 == 1
    assert FIRST > 11
    assert (4 * FIRST - 1) % (5 * 479) == 0
    assert (2 * FIRST - 1) % (3 * 7) == 0
    assert STEP % (5 * 479) == STEP % (3 * 7) == 0

    assert ODD_MODULUS == 3 * 5 * 7 * 11**2 * 479
    assert TARGET % 2 == 0 and TARGET % 5 == 4 and TARGET % 7 == 5
    squares7 = {x * x % 7 for x in range(1, 7)}
    assert 2 in squares7 and 26 % 7 == 5 and 5 not in squares7
    assert pow(2, 29_024, ODD_MODULUS) == 26**2
    assert 26 * pow(2, BASE_EXPONENT, ODD_MODULUS) % ODD_MODULUS == TARGET % ODD_MODULUS
    primes = (2, 3, 5, 11, 239)
    assert all(all(p % d for d in range(2, isqrt(p) + 1)) for p in primes)
    assert DIRECT_PERIOD == 2**2 * 3 * 5 * 11 * 239
    assert pow(2, DIRECT_PERIOD, ODD_MODULUS) == 1
    assert all(pow(2, DIRECT_PERIOD // p, ODD_MODULUS) != 1 for p in primes)

    modulus = ODD_MODULUS * 13 * 19
    assert modulus == 1_503_166_665
    assert pow(2, DISJOINT_PERIOD, modulus) == 1
    assert pow(2, BASE_EXPONENT, modulus) == 197_935_984
    assert (52 * pow(2, BASE_EXPONENT, STEP) + 1) % STEP == FIRST

    # The four recorded older families are distinguished by t modulo 13 or 19.
    old_modulus = 50_295 * 13 * 19
    old_direct = pow(2, 82, old_modulus) * pow(26, 33, old_modulus) % old_modulus
    assert pow(2, 8_604, old_modulus) == 1
    assert (2 * old_direct + 1) % 19 == 16
    old_modulus = 4 * 100_590 * 13 * 19 * 23
    old_q = pow(3, 217, old_modulus)
    assert old_modulus % 9 != 0 and pow(3, 94_644, old_modulus // 3) == 1
    assert old_q % 4 == 3
    assert ((2 * 2**2 * 26**5 + 1) * ((old_q + 1) // 4)) % 19 == 13

    assert (52 * pow(2, BASE_EXPONENT, 13) + 1) % 13 == 1
    assert (52 * pow(2, BASE_EXPONENT, 19) + 1) % 19 == 4
    assert pow(2, 6, 19) == 26 % 19 and len({pow(2, x, 19) for x in range(18)}) == 18
    assert ((BASE_EXPONENT + 6) % 18, (12 - 29_024) % 18, DIRECT_PERIOD % 18) == (12, 4, 6)
    residues = {(1 + 2 * pow(2, (12 + 4*j + 6*z) % 18, 19)) % 19
                for j in range(3) for z in range(3)}
    assert residues == {0, 3, 4, 9, 11, 13, 14, 15, 16}
    squares19 = {x * x % 19 for x in range(19)}
    disjoint = residues - {0, 13, 16}
    certify_scarpis = {t for t in disjoint if (16 * t + 1) % 19 not in squares19}
    assert certify_scarpis == {4, 9, 15}
    for j, first, residue in ((0, 83_022, 4), (2, 24_974, 9), (0, 398_502, 15)):
        assert (first + 29_024 * j - BASE_EXPONENT) % DIRECT_PERIOD == 0
        assert (1 + 2 * pow(2, first, 19) * pow(26, 2*j + 1, 19)) % 19 == residue
        assert (1 + 2 * pow(2, first, STEP) * pow(26, 2*j + 1, STEP)) % STEP == FIRST
    print("direct Golay AP: b=0, c=2j+1, a+29024j=83022 mod 157740; t mod 19 =",
          sorted(residues))


def golay_product(outer, inner):
    left, right = outer
    c, d = inner
    reverse_c, reverse_d = c[::-1], d[::-1]
    f, g = [], []
    for a, b in zip(left, right, strict=True):
        if a == b:
            f.extend(a * value for value in c)
            g.extend(a * value for value in d)
        else:
            f.extend(a * value for value in reverse_d)
            g.extend(-a * value for value in reverse_c)
    return tuple(f), tuple(g)


def check_control():
    seed2 = ((1, 1), (1, -1))
    assert aperiodic(seed2) == [4, 0]
    assert aperiodic(GOLAY_26) == [52] + [0] * 25
    left, right = golay_product(seed2, GOLAY_26)
    g = len(left)
    assert len(right) == g == 52 and all(abs(value) == 1 for word in (left, right) for value in word)
    assert aperiodic((left, right)) == [2*g] + [0] * (g - 1)
    t = 2*g + 1
    selectors = (left + (0,) * (g + 1),
                 (0,) * g + (1,) + (0,) * g,
                 (0,) * (g + 1) + right,
                 (0,) * t)
    assert aperiodic(selectors) == [t] + [0] * (t - 1)
    assert all(sum(map(abs, values)) == 1 for values in zip(*selectors, strict=True))
    words = [
        tuple(sum((-1)**((row & col).bit_count()) * value for col, value in enumerate(values))
              for values in zip(*selectors, strict=True))
        for row in range(4)
    ]
    assert all(abs(value) == 1 for word in words for value in word)
    assert aperiodic(words) == [4*t] + [0] * (t - 1)
    n = 4*t
    columns = goethals_seidel(words)
    assert len(columns) == n == 420 and verify_orthogonal(n, columns) == 87_990

    all_plus = (1 << n) - 1
    normalized = [word if word & 1 else word ^ all_plus for word in columns]
    row_signs = normalized[0] ^ all_plus
    normalized = [word ^ row_signs for word in normalized]
    selected = [word >> 2 for word in normalized if not (word >> 1 & 1)]
    assert len(selected) == 2*t
    assert all(row.bit_count() == t for row in rows_from_columns(n - 2, selected))
    assert all(word.bit_count() == 2*t - 1 for word in selected)
    assert all((a & b).bit_count() == t - 1 for a, b in combinations(selected, 2))
    assert comb(len(selected), 2) == 21_945 and t % 4 == 1 and t % 9 == 6
    print("Golay product control: H(420), 87990 orthogonal column pairs; R(105), 21945 point pairs")


if __name__ == "__main__":
    check_arithmetic()
    check_control()
