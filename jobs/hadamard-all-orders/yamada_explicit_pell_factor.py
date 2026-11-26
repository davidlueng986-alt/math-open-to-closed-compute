#!/usr/bin/env python3
"""Validate the giant explicit Pell factor and forced change of local type."""

from fractions import Fraction
from math import gcd, isqrt, prod


def main():
    r = 307076037508906904285239
    n = 2 * r + 1
    x, y = -293700983222361, -207677217568161
    original_x, original_y = 1586879471199, 975713682669
    for _ in range(3):
        original_x, original_y = 3 * original_x + 4 * original_y, 2 * original_x + 3 * original_y
    assert (x, y) == (-original_x, -original_y)
    assert x * x - 2 * y * y == n and x % 4 == 3 and y % 2
    denominator = (x - 1) // 2
    p = abs(denominator)
    assert p == 146850491611181
    factors = ((2, 2), (5, 1), (7, 1), (61, 1), (79, 1), (83, 1), (269, 1), (9749, 1))
    assert prod(q ** exponent for q, exponent in factors) == p - 1
    assert all(all(q % d for d in range(2, isqrt(q) + 1)) for q, _ in factors)
    assert pow(2, p - 1, p) == 1
    assert all(gcd(pow(2, (p - 1) // q, p) - 1, p) == 1 for q, _ in factors)

    a, b = Fraction(n - x, x - 1), Fraction(2 * y, x - 1)
    j = -Fraction(1, denominator)
    assert a + r * j == -1
    assert a * a + r * b * b == n
    numerator_i = (n - x) // 2
    assert denominator % 2 == 1
    assert (numerator_i - 1) % 2 == 1
    assert (y - 1) % 2 == (-y - 1) % 2 == 0
    assert gcd(p, gcd(y - 1, -y - 1)) == 1

    bound = isqrt(r - 1)
    assert bound == 554144419360
    for ell in (3, 11):
        assert denominator % ell and n % (ell * ell) == 0 and n % (ell ** 3)
        assert pow(2, (ell - 1) // 2, ell) == ell - 1
        assert numerator_i % ell == y % ell == 0
        assert pow(-r % ell, (ell - 1) // 2, ell) == ell - 1
        assert (r - 3) // 2 > bound
    vector = (6, -5, -2, 1)
    assert sum(vector) == 0 and sum(value * value for value in vector) == 66
    odd = {i for i, value in enumerate(vector) if value % 2}
    assert odd == {1, 3}
    reflection = [[Fraction(i == j) - Fraction(x * y, 33)
                   for j, y in enumerate(vector)] for i, x in enumerate(vector)]
    transposed = [reflection[i] for i in (0, 3, 2, 1)]
    assert all(sum(row) == 1 for row in transposed)
    assert all(sum(x * y for x, y in zip(row, other)) == (i == j)
               for i, row in enumerate(transposed) for j, other in enumerate(transposed))
    assert all(value.denominator % 2 and value.numerator % 2 == (i == j)
               for i, row in enumerate(transposed) for j, value in enumerate(row))
    for ell in (3, 11):
        # On the three difference-basis vectors, only the outer product
        # survives after multiplying by ell and reducing modulo ell.
        image = []
        for j in range(3):
            column = [ell * (row[j] - row[3]) for row in transposed]
            image.append(tuple(value.numerator * pow(value.denominator, -1, ell) % ell
                               for value in column))
        direction = next(column for column in image if any(column))
        line = {tuple(c * value % ell for value in direction) for c in range(ell)}
        assert all(column in line for column in image)
    assert numerator_i % 33 == y % 33 == 0
    blocks = r // 4
    assert blocks >= bound
    print(f"YAMADA-PELL-FACTOR-PASS denominator={p} inert=[3, 11] "
          f"endpoint_rank={bound} block_limit={blocks}")


if __name__ == "__main__":
    main()
