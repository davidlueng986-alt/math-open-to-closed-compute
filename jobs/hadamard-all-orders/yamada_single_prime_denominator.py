#!/usr/bin/env python3
"""Exact checks for unit spinor classes and a one-prime denominator control."""

from fractions import Fraction
from math import lcm


def dot(left, right):
    return sum(x * y for x, y in zip(left, right))


def orthogonal_reflection_on_vector(vector, target):
    coefficient = Fraction(2 * dot(vector, target), dot(vector, vector))
    return [x - coefficient * v for x, v in zip(target, vector)]


def product_on_columns(left, right, matrix):
    return list(
        zip(
            *(
                orthogonal_reflection_on_vector(
                    left, orthogonal_reflection_on_vector(right, column)
                )
                for column in zip(*matrix)
            )
        )
    )


def reduction_mod_two(value):
    value = Fraction(value)
    assert value.denominator % 2
    return value.numerator % 2


def parity_identity(matrix):
    return all(
        reduction_mod_two(value) == (i == j)
        for i, row in enumerate(matrix)
        for j, value in enumerate(row)
    )


def check_factor(matrix):
    r = len(matrix)
    columns = list(zip(*matrix))
    assert all(sum(row) == -1 for row in matrix)
    assert all(sum(column) == -1 for column in columns)
    assert all(
        dot(columns[i], columns[j]) == ((2 * r + 1) * (i == j) - 2)
        for i in range(r)
        for j in range(i, r)
    )
    assert parity_identity(matrix)


def paley_factor_23():
    q = 23
    positive = {i * i % q for i in range(1, q)}

    def character(x):
        residue = x % q
        return 0 if not residue else (1 if residue in positive else -1)

    order = sorted(positive)
    return [
        [character(y - x) - character(-y - x) for y in order]
        for x in order
    ]


def main():
    matrix = paley_factor_23()
    r = len(matrix)
    check_factor(matrix)
    lookup = ((1, -1), (1, 1, -2), (1, -1, 2, -2), (1, 1, -2, 2, -2))
    vectors = [list(v) + [0] * (r - len(v)) for v in lookup]
    v = vectors[0]
    classes = []
    for w in vectors:
        assert sum(v) == sum(w) == 0
        assert [x % 2 for x in v] == [x % 2 for x in w]
        assert dot(v, v) == 2
        classes.append((dot(v, v) * dot(w, w) // 4) % 8)
        assert parity_identity(product_on_columns(v, w, matrix))
    assert classes == [1, 3, 5, 7]

    transformed = product_on_columns(v, vectors[2], matrix)
    check_factor(transformed)
    denominator = lcm(*(value.denominator for row in transformed for value in row))
    assert denominator == 5
    print(f"YAMADA-SINGLE-PRIME-PASS r={r} spinor_units={classes} denominator={denominator}")


if __name__ == "__main__":
    main()
