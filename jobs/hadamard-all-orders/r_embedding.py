"""Verify exact variance and equitable-cut bounds for the two 2396 spectra."""

from fractions import Fraction


def minimal_variance(mean, residue, modulus):
    offset = (mean - residue) % modulus
    return offset * (modulus - offset)


def verify():
    t = 599
    n = 2 * t - 1
    for gap, degree, positive_residue, equitable_upper in (
        (4, 391, 5, 1147),
        (10, 271, 17, 823),
    ):
        modulus = 2 * gap
        mean = -Fraction(27 * degree, t)
        other_mean = (-degree - n * mean) / (n - 1)
        energy = 2 * n * degree - degree**2 - n * mean**2 - (n - 1) * other_mean**2

        offset = (mean - positive_residue) % modulus
        distance = min(offset, modulus - offset)
        equitable_bound = n * energy / (energy + n * distance**2)
        assert equitable_upper <= equitable_bound < equitable_upper + 1

        positive_mean = other_mean - (degree - other_mean) / n
        negative_mean = other_mean + (degree - other_mean) / n
        outer_min = n * minimal_variance(mean, positive_residue, modulus)
        inner_min = (
            Fraction(n * (n - 1), 2 * (n + 1))
            * minimal_variance(positive_mean, positive_residue, modulus)
            + Fraction(n, 2) * minimal_variance(negative_mean, 3, modulus)
        )
        if gap == 10:
            assert energy == outer_min + inner_min
            assert -23 < mean < -3
            assert -3 < positive_mean < 17
            assert 3 < negative_mean < 23
        else:
            assert energy > outer_min + inner_min

    assert 626 * 271 == 137 * 1198 + 10 * 552
    assert 572 * 271 == 127 * 598 + 124 * 599 + 10 * (156 + 323)
    assert 17 * 598 - 23 * 599 + 20 * (323 - 156) == -271
    assert 10 * 208 - 13 * 137 == 10 * 221 - 13 * 147 == 299
    assert 1198 - 552 == 646
    assert next(k for k in range(552, 1199)
                if 2394 * (k - 552)**2 >= 2 * k * (1198 - k)) == 570
    assert 1198 - 570 == 628
    assert [(47920 * int(i == 0) - 23 * dot + 254 - 2396 * int(i == 1)) // 20
            for i, dot in enumerate((1198, -54, -2, 38))] == [1031, -45, 15, -31]
    assert 156 - 323 == -167


if __name__ == "__main__":
    verify()
    print("Verified the exact equitable-cut bounds and embedding variance saturation.")
