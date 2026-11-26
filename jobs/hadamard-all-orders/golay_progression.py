"""Check the Golay progression arithmetic and reconstruct a 212-order control."""

from t599_length_change import GOLAY_26, aperiodic
from verify import goethals_seidel, verify_orthogonal


def check_progression():
    modulus = 50295 * 13 * 19
    residue = pow(2, 82, modulus) * pow(26, 33, modulus) % modulus
    assert pow(2, 8604, modulus) == 1 and residue == 9153989
    t = 2 * residue + 1
    assert (t % 100590, t % 13, t % 19) == (599, 1, 16)
    assert (4*t - 1) % (5*479) == (2*t - 1) % (3*7) == 0
    assert (16*t + 1) % 19 == 10 and all(x*x % 19 != 10 for x in range(19))
    print("Golay progression: t = 599 mod 100590, disjoint from the T13 and T19 families")

    modulus = 4 * 100590 * 13 * 19 * 23
    residue = pow(3, 217, modulus)
    assert residue == 1674778563 and residue % 8 == 3 and residue % 3 == 0
    assert pow(3, 94644, modulus // 3) == 1
    width = 2 * 2**2 * 26**5 + 1
    assert width == 95051009
    t = width * ((residue + 1) // 4)
    assert (t % 100590, t % 13, t % 19) == (599, 1, 13)
    assert (16*t + 1) % 23 == 20 and all(x*x % 23 != 20 for x in range(23))
    print("Golay–Paley progression: forced prime powers of three give a fourth disjoint family")


def check_seed_matrix():
    left, right = GOLAY_26
    g = len(left)
    size = 2*g + 1
    assert len(right) == g == 26
    assert aperiodic(GOLAY_26) == [2*g] + [0] * (g - 1)
    t_words = (
        left + (0,) * (g + 1),
        (0,) * g + (1,) + (0,) * g,
        (0,) * (g + 1) + right,
        (0,) * size,
    )
    assert aperiodic(t_words) == [size] + [0] * (size - 1)
    assert all(sum(abs(value) for value in col) == 1 for col in zip(*t_words, strict=True))
    words = [
        tuple(sum((-1)**((row & col).bit_count()) * value for col, value in enumerate(values))
              for values in zip(*t_words, strict=True))
        for row in range(4)
    ]
    assert all(abs(x) == 1 for word in words for x in word)
    assert aperiodic(words) == [4*size] + [0] * (size - 1)
    columns = goethals_seidel(words)
    assert len(columns) == 212 and verify_orthogonal(212, columns) == 22366
    print("Golay length 26 control: reconstructed H(212), all 22,366 column products zero")


if __name__ == "__main__":
    check_progression()
    check_seed_matrix()
