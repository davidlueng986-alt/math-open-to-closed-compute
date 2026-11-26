"""Verify the source and sharp residual gap controls for the odd-order stack."""

from itertools import product
from math import isqrt

from verify import paley, rows_from_columns, verify_orthogonal


def conference_positive_columns(prime):
    """Pack the positive entries of the symmetric Paley conference matrix."""
    assert prime % 4 == 1 and all(prime % d for d in range(2, isqrt(prime) + 1))
    squares = {i * i % prime for i in range(1, prime)}
    size = prime + 1
    universe = (1 << size) - 1
    return [universe ^ 1] + [
        1 + sum(1 << (i + 1) for i in range(prime) if (i - j) % prime in squares)
        for j in range(prime)]


def paley_type_two(prime):
    conference_positive = conference_positive_columns(prime)
    size = len(conference_positive)
    universe = (1 << size) - 1
    plus = [word | 1 << j for j, word in enumerate(conference_positive)]
    minus = conference_positive
    return [a | (b << size) for a, b in zip(plus, minus, strict=True)] + [
        b | ((a ^ universe) << size) for a, b in zip(plus, minus, strict=True)]


def sylvester_four(columns):
    size = len(columns)
    universe = (1 << size) - 1
    return [sum((word ^ (universe if (row & col).bit_count() % 2 else 0)) << (size * row)
                for row in range(4)) for col in range(4) for word in columns]


def check_gap_controls(columns):
    size = len(columns)
    d = size // 4
    universe = (1 << size) - 1
    negative = [word ^ universe for word in columns]
    parity_kernel = [p for p in range(1 << size) if p.bit_count() % 2 == 0
                     and all((p & word).bit_count() % 2 == 0 for word in negative)]
    assert parity_kernel == [0, universe]
    rows = rows_from_columns(size, columns)
    s = [((rows[0] >> j & 1) + (rows[1] >> j & 1)) - 1 for j in range(size)]
    assert sum(value**2 for value in s) == 2 * d
    for i, row in enumerate(rows):
        dot = sum(value * (2 * (row >> j & 1) - 1) for j, value in enumerate(s))
        assert dot == (2 * d if i < 2 else 0)


def main():
    controls = [paley(11), paley_type_two(149)]
    assert [verify_orthogonal(len(columns), columns) for columns in controls] == [66, 44850]
    check_gap_controls(controls[0])
    full = sylvester_four(controls[1])
    assert verify_orthogonal(len(full), full) == 719400
    for coefficients in product(range(5), repeat=4):
        transformed = [sum(a * (-1 if (i & j).bit_count() % 2 else 1)
                           for j, a in enumerate(coefficients)) for i in range(4)]
        assert any(value % 5 for value in transformed) == any(coefficients)
    print('Uniform odd stack: the H12 control attains squared kernel length 6 modulo 3')
    print('Alternate H1200: four H300 channels, 719400 exact products, modulus 75 and gap 2400 per channel')


if __name__ == '__main__':
    main()
