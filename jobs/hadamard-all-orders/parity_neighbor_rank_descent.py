"""Replay finite controls of simultaneous odd-prime neighbor descent."""

from fractions import Fraction

from yamada_single_prime_denominator import check_factor, paley_factor_23


def transform(rows, group):
    """Apply the constant-block reflection on one coordinate group."""
    average = tuple(2 * sum(rows[i][j] for i in group) / len(group)
                    for j in range(len(rows[0])))
    return [tuple(x - y for x, y in zip(average, row, strict=True)) if i in group else row
            for i, row in enumerate(rows)]


def numerator(rows, denominator):
    scaled = tuple(tuple(denominator * x for x in row) for row in rows)
    assert all(x.denominator == 1 for row in scaled for x in row)
    return tuple(tuple(int(x) for x in row) for row in scaled)


def column_basis(rows, prime):
    """Eliminate columns over the prime field, retaining lifts in the integer column span."""
    basis = {}
    for column in zip(*rows, strict=True):
        vector = list(column)
        for pivot, previous in basis.items():
            scalar = vector[pivot] % prime
            if scalar:
                vector = [a - scalar*b for a, b in zip(vector, previous, strict=True)]
        pivot = next((i for i, value in enumerate(vector) if value % prime), None)
        if pivot is not None:
            inverse = pow(vector[pivot], -1, prime)
            basis[pivot] = tuple(inverse * value for value in vector)
    return basis


def lift_indicator(group, basis, length, prime):
    indicator = tuple(int(i in group) for i in range(length))
    remainder = list(indicator)
    for pivot, column in basis.items():
        scalar = remainder[pivot] % prime
        if scalar:
            remainder = [a - scalar*b for a, b in zip(remainder, column, strict=True)]
    assert not any(value % prime for value in remainder)
    return tuple(a-b for a, b in zip(indicator, remainder, strict=True))


def three_control(original):
    seed = ((0, 3, 5), (1, 5, 7), (6, 8, 9), (0, 2, 4), (0, 1, 2))
    factor = original
    for group in seed:
        factor = transform(factor, group)
    check_factor(factor)
    before = column_basis(numerator(factor, 9), 3)
    assert len(before) == 2

    groups = ((4, 5, 7), (0, 1, 2))
    assert set(groups[0]).isdisjoint(groups[1])
    lifts = tuple(lift_indicator(group, before, len(factor), 3) for group in groups)
    for i, left in enumerate(groups):
        rotated = transform(factor, left)
        check_factor(rotated)
        assert len(column_basis(numerator(rotated, 9), 3)) == 1
        cross = sum(lifts[i][j] for j in groups[1-i])
        assert cross % 3 == 0 and cross // 3 % 3 == (2, 1)[i]

    rotated = transform(transform(factor, groups[0]), groups[1])
    check_factor(rotated)
    assert len(column_basis(numerator(rotated, 9), 3)) == 2
    print("P=3 actual denominator 9, rank 2; each move leaves rank 1; joint move leaves rank 2")


def five_control(original):
    group = tuple(range(5))
    factor = transform(original, group)
    check_factor(factor)
    basis = column_basis(numerator(factor, 5), 5)
    assert len(basis) == 1
    lift_indicator(group, basis, len(factor), 5)
    assert transform(factor, group) == original
    print("P=5 constant-block move: rank 1 -> 0 and integral factor recovered")


def second_layer_control(original):
    seed = ((0, 5, 7), (0, 4, 8), (4, 6, 10), (4, 5, 9), (1, 4, 5), (6, 8, 9))
    factor = original
    for group in seed:
        factor = transform(factor, group)
    check_factor(factor)
    scaled = numerator(factor, 243)
    basis = column_basis(scaled, 3)
    (pivot, vector), = basis.items()
    reduced = tuple(x % 3 for x in vector)
    assert reduced == (0, 1, 0, 0, 1, 1, 2, 0, 2, 2, 0)
    groups = seed[-2:]
    for group in groups:
        assert sum(vector[i] for i in group) % 3 == 0
        for col in zip(*scaled, strict=True):
            lifted = tuple(a - (col[pivot] % 3)*b for a, b in zip(col, vector, strict=True))
            assert all(x % 3 == 0 for x in lifted)
            assert sum(lifted[i] for i in group) % 9 == 0
        rotated = transform(factor, group)
        check_factor(rotated)
        assert len(column_basis(numerator(rotated, 243), 3)) == 1
    rotated = transform(transform(factor, groups[0]), groups[1])
    check_factor(rotated)
    assert len(column_basis(numerator(rotated, 243), 3)) == 0
    assert len(column_basis(numerator(rotated, 81), 3)) == 1

    factor = transform(original, (0, 1, 2))
    assert len(column_basis(numerator(factor, 3), 3)) == 1
    rotated = transform(factor, (3, 4, 5))
    assert len(column_basis(numerator(rotated, 3), 3)) == 2
    print("P=3 weight-6 residual: separate moves keep rank 1, combined exponent 5 -> 4")


def main():
    original = [tuple(Fraction(x) for x in row) for row in paley_factor_23()]
    three_control(original)
    five_control(original)
    second_layer_control(original)


if __name__ == '__main__':
    main()
