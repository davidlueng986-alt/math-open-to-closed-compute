#!/usr/bin/env python3
"""Exact small Paley-double check of its intrinsic pair system."""
from itertools import combinations
from math import comb


def product(a, b):
    return tuple(
        tuple(sum(x * y for x, y in zip(row, col)) for col in zip(*b))
        for row in a
    )


def paley(q):
    positive = {i * i % q for i in range(1, q)}
    return [[0] + [1] * q] + [
        [-1] + [0 if i == j else (1 if (j - i) % q in positive else -1)
                for j in range(q)]
        for i in range(q)
    ]


def double(matrix, h, j):
    v = len(matrix)
    return [
        [matrix[a][b] * h[i][k] + (a == b) * j[i][k] for b in range(v) for k in range(2)]
        for a in range(v) for i in range(2)
    ]


def closed_fours(matrix):
    size = len(matrix)
    all_bits = (1 << size) - 1
    negatives = [sum(1 << j for j, v in enumerate(row) if v == -1) for row in matrix]
    for a, b, c, d in combinations(range(size), 4):
        outside = all_bits ^ ((1 << a) | (1 << b) | (1 << c) | (1 << d))
        parity = outside & (negatives[a] ^ negatives[b] ^ negatives[c] ^ negatives[d])
        if parity in (0, outside):
            yield a, b, c, d


def main():
    h = ((1, 1), (1, -1))
    j = ((0, 1), (-1, 0))
    diag = ((1, 0), (0, -1))
    swap = ((0, 1), (1, 0))
    assert product(product(h, diag), h) == tuple(tuple(2 * x for x in row) for row in swap)
    assert product(product(h, swap), h) == tuple(tuple(2 * x for x in row) for row in diag)
    base = paley(19)
    matrix = double(base, h, j)
    size = len(matrix)
    assert all(matrix[i][i] == 0 for i in range(size))
    assert all(abs(matrix[i][k]) == 1 and matrix[i][k] == -matrix[k][i]
               for i in range(size) for k in range(i + 1, size))
    assert all(sum(x * y for x, y in zip(matrix[i], matrix[k])) == ((size - 1) * (i == k))
               for i in range(size) for k in range(i, size))
    actual = set(closed_fours(matrix))
    expected = {(2 * a, 2 * a + 1, 2 * b, 2 * b + 1)
                for a, b in combinations(range(len(base)), 2)}
    assert actual == expected
    print(f"YAMADA-PALEY-DOUBLE-PASS order={size} subsets={comb(size, 4)} closed={len(actual)}")


if __name__ == "__main__":
    main()
