"""Replay the small exact cases and an affine sign certificate for all larger r."""

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import prod


@dataclass(frozen=True)
class Affine:
    a: int = 0
    b: int = 0

    def __call__(self, r):
        return self.a * r + self.b

    def __add__(self, other):
        return Affine(self.a + other.a, self.b + other.b)

    def __neg__(self):
        return Affine(-self.a, -self.b)

    def __sub__(self, other):
        return self + -other

    def __mul__(self, k):
        return Affine(self.a * k, self.b * k)

    def nonnegative_for(self, low):
        return self.a >= 0 and self(low) >= 0


X = Affine(a=1)
C = lambda b: Affine(b=b)
LENGTH = X * 4 + C(3)
U = X * 2 + C(1)
TETRAD = ((1, U), (1, U + C(1)), (3, U), (3, U + C(1)))
J = ((0, C(0)), (0, C(1)), (0, X + C(1)), (0, U + C(1)),
     (1, U), (1, X * 3 + C(2)),
     (2, C(0)), (2, U), (2, X * 3 + C(2)), (2, LENGTH - C(1)),
     (3, U), (3, X * 3 + C(2)))
# Sequence, j multiplier, i multiplier, sign.
BLOCKS = (((0, 1, -1, 1), (1, -1, -1, -1), (2, -1, -1, -1), (3, -1, -1, -1)),
          ((1, -1, -1, 1), (0, 1, -1, 1), (3, 1, 1, -1), (2, 1, 1, 1)),
          ((2, -1, -1, 1), (3, 1, 1, 1), (0, 1, -1, 1), (1, 1, 1, -1)),
          ((3, -1, -1, 1), (2, 1, 1, -1), (1, 1, 1, 1), (0, 1, -1, 1)))


def determinant(rows):
    matrix = [[Fraction(c) for c in row] for row in rows]
    result = Fraction(1)
    for j in range(len(matrix)):
        i = next((i for i in range(j, len(matrix)) if matrix[i][j]), None)
        if i is None:
            return 0
        if i != j:
            matrix[i], matrix[j] = matrix[j], matrix[i]
            result *= -1
        pivot = matrix[j][j]
        result *= pivot
        for i in range(j + 1, len(matrix)):
            factor = matrix[i][j] / pivot
            matrix[i] = [a - factor * b for a, b in zip(matrix[i], matrix[j], strict=True)]
    assert result.denominator == 1
    return result.numerator


def sign_of_source(seq, j, r0, symbolic):
    odd = bool(r0 % 2)

    def assert_interval(lower, upper):
        if symbolic:
            assert (j - lower).nonnegative_for(r0), (seq, j, r0, lower)
            assert (upper - j - C(1)).nonnegative_for(r0), (seq, j, r0, upper)

    if j(r0) == U(r0):
        assert_interval(U, U + C(1))
        return (1 if odd else -1) * (1 if seq != 3 else -1)
    if j(r0) < U(r0):
        assert_interval(C(0), U)
        head = 0 if seq in (0, 1) else 1
        multiplier = 1
    else:
        assert_interval(U + C(1), LENGTH)
        head = 0 if seq in (0, 2) else 1
        j = LENGTH - C(1) - j
        multiplier = -1 if j(r0) % 2 == 0 else 1

    if odd:
        if head == 0:
            pieces = ((C(0), X - C(1), 1), (X - C(1), X, -1),
                      (X, X + C(2), 1), (X + C(2), U, None))
        else:
            pieces = ((C(0), X - C(1), -1), (X - C(1), X, 1), (X, X + C(1), -1),
                      (X + C(1), X + C(2), 1), (X + C(2), U, None))
    elif head == 0:
        pieces = ((C(0), U, 1),)
    else:
        pieces = ((C(0), X + C(1), -1), (X + C(1), U, 1))
    for lower, upper, sign in pieces:
        if lower(r0) <= j(r0) < upper(r0):
            assert_interval(lower, upper)
            if sign is None:
                sign = 1 if j(r0) % 2 == 0 else -1
            return sign * multiplier
    raise AssertionError(("source arg", seq, j, r0))


def entry(row, col, r0, symbolic=False):
    i_block, i = row
    j_block, j = col
    seq, j_sign, i_sign, multiplier = BLOCKS[i_block][j_block]
    raw = j * j_sign + i * i_sign
    quotient = raw(r0) // LENGTH(r0)
    index = raw - LENGTH * quotient
    if symbolic:
        assert index.nonnegative_for(r0), (r0, row, col, index)
        assert (LENGTH - C(1) - index).nonnegative_for(r0), (r0, row, col, index)
    return multiplier * sign_of_source(seq, index, r0, symbolic)


def minor_stability():
    even_rows = tuple((0, j) for j in (
        C(0), C(1), C(2), C(3), X + C(2), X + C(3), U + C(1),
        U + C(2), X * 3 + C(3), X * 3 + C(4))) + ((1, C(0)), (1, C(1)))
    odd_rows = tuple((0, j) for j in (
        C(0), C(1), C(4), C(3), U + C(2), X + C(2), X, X + C(5),
        U + C(3), X + C(1), X * 3 + C(3), X * 3 + C(4)))
    for r0, rows, magnitude in ((4, even_rows, 8192), (7, odd_rows, 16384)):
        matrix = [[entry(row, col, r0, symbolic=True) for col in J] for row in rows]
        assert abs(determinant(matrix)) == magnitude
        print(f"r≥{r0}, r≡{r0 % 2} mod2, stable minor |det|={magnitude}")
        print("  ", " ".join(f"{sum(int(x < 0) << i for i, x in enumerate(row)):03x}" for row in matrix))


SMALL_MINORS = {
    1: ((0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12), 8192),
    2: ((0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12), 8192),
    3: ((0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13), 16384),
    5: ((0, 1, 4, 3, 13, 7, 5, 10, 14, 6, 18, 19), 16384),
}


def small_case(r):
    t = LENGTH(r)
    n = 4 * t
    idx = lambda row: row[0] * t + row[1](r)
    pairs = [(b, C(j)) for b in range(4) for j in range(t)]
    H = [[entry(i, j, r) for j in pairs] for i in pairs]
    if r <= 3:
        assert all(sum(a * b for a, b in zip(x, y, strict=True)) == n * int(i == j)
                   for i, x in enumerate(H) for j, y in enumerate(H))
    I = [idx(x) for x in TETRAD]
    J0 = [idx(x) for x in J]
    assert [j for j in range(n) if prod(H[i][j] for i in I) < 0] == J0
    normalizer = r if r > 1 else 3
    for row in H:
        flip = row[normalizer]
        for j in range(n):
            row[j] *= flip
    half_sums = [sum(H[i][j] for i in I) // 2 for j in range(n)]
    for i in I:
        H[i] = [half_sums[j] - x for j, x in enumerate(H[i])]
    R = [[row[j] for j in J0] for row in H]
    indices, value = SMALL_MINORS[r]
    assert abs(determinant([R[i] for i in indices])) == value
    assert all(sum(row) == 0 for row in zip(*R, strict=True))
    assert all(sum(x * x for x in row) == 12 for row in R)
    assert all(all(row[j] in (-1, 1) for j in range(n) if j not in J0) for row in H)
    print(f"r={r}, n={n}: {'exact' if r <= 3 else 'modular'} case minor rows={indices}, |det|={value}")


if __name__ == "__main__":
    minor_stability()
    for r in SMALL_MINORS:
        small_case(r)
