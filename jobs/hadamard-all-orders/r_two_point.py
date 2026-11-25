"""Verify the exact constants in the 2396 two-point kernel bounds."""

from fractions import Fraction
from math import comb, prod


def falling(value, degree):
    return prod(range(value - degree + 1, value + 1))


def johnson_numerator(block_size, overlap, degree):
    return sum(
        (-1) ** (degree - j)
        * comb(degree, j)
        * (falling(overlap, j) * falling(block_size - overlap, degree - j)) ** 2
        for j in range(degree + 1)
    )


def verify():
    block_size = 599
    off_diagonal_count = 4 * block_size - 3
    overlaps = (286, 299, 303, 309)
    for degree in range(3, 12):
        denominator = falling(block_size, degree) ** 2
        for overlap in overlaps:
            numerator = johnson_numerator(block_size, overlap, degree)
            assert off_diagonal_count * abs(numerator) < denominator

    max_deviation = Fraction(19, 588)
    mismatch_probability = Fraction(1, 2) + 2 * max_deviation**2
    assert off_diagonal_count * mismatch_probability**12 < 1

    dimension = 2 * block_size - 1
    coherence = Fraction(27, 599)
    cubic = ((dimension + 2) * coherence**3 + 3 * coherence) / (dimension - 1)
    quartic = (
        coherence**4
        + 2 * coherence**2 / (dimension - 1)
        + Fraction(3, (dimension - 1) * (dimension + 1))
    )
    assert off_diagonal_count * cubic < 1
    assert off_diagonal_count * quartic < 1


if __name__ == "__main__":
    verify()
    print("Verified the exact Johnson and spherical two-point kernel bounds.")
