#!/usr/bin/env python3
"""Replay short-reflection descent and small 3-neighbor norm-one counts."""
from fractions import Fraction
from itertools import combinations

from yamada_single_prime_denominator import (
    check_factor,
    dot,
    orthogonal_reflection_on_vector,
    paley_factor_23,
    product_on_columns,
)


def verify_denominator_descent():
    matrix = paley_factor_23()
    r = len(matrix)
    v = (1, -1) + (0,) * (r - 2)
    w = (1, -1, 2, -2) + (0,) * (r - 4)
    rational = product_on_columns(v, w, matrix)
    check_factor(rational)
    short = orthogonal_reflection_on_vector(v, w)
    assert all(a.denominator == 1 for a in short)
    assert sum(short) == 0 and dot(short, short) == 10
    scaled = [[5 * entry for entry in row] for row in rational]
    assert all(entry.denominator == 1 for row in scaled for entry in row)
    short_reduced = tuple(int(a) % 5 for a in short)
    line = {tuple(t * a % 5 for a in short_reduced) for t in range(5)}
    columns_reduced = {tuple(int(a) % 5 for a in column) for column in zip(*scaled)}
    assert columns_reduced.issubset(line)
    assert any(any(column) for column in columns_reduced)
    recovered = product_on_columns(v, short, rational)
    assert recovered == [tuple(Fraction(a) for a in row) for row in matrix]


def count_neighbor_lines(m):
    vector = [1] * m
    # Raise the squared norm to a multiple of 9 by replacing one coordinate
    # with an integer congruent to 1 mod 3.
    vector[0] = next(x for x in (-2, 1, 4) if (m - 1 + x * x) % 9 == 0)
    results = []
    for count in range(m + 1):
        for doubled in combinations(range(m), count):
            u = [-2 if i in doubled else 1 for i in range(m)]
            if dot(u, u) != 9:
                continue
            difference = [(a - b) // 3 for a, b in zip(u, vector)]
            assert dot(difference, vector) % 3 == 0
            results.append(sum(a % 2 for a in u))
    return len(results), sorted(set(results))


def main():
    verify_denominator_descent()
    results = {m: count_neighbor_lines(m) for m in (3, 6, 9, 12)}
    assert results == {3: (3, [1]), 6: (6, [5]), 9: (1, [9]), 12: (0, [])}
    print(f"YAMADA-DENOMINATOR-DESCENT-PASS p=5 rank=1->0 neighbors3={results}")


if __name__ == "__main__":
    main()
