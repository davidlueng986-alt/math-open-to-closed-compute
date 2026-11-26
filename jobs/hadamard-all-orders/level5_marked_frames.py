#!/usr/bin/env python3
"""Exact replay of terminal level-five marked standard frames."""

import json
from itertools import product
from pathlib import Path


def dot(left, right):
    return sum(a * b for a, b in zip(left, right))


def transpose(rows):
    return list(zip(*rows))


def multiply(left, right):
    columns = transpose(right)
    return [[dot(row, column) for column in columns] for row in left]


def k5_vectors():
    vectors = []
    for i in range(5):
        for step in (1, 2):
            j = (i + step) % 5
            vectors.append(tuple(2 * ((k == j) - (k == i)) for k in range(5)))
    return vectors


def marked_frame(doubled):
    count = len(doubled)
    assert all(dot(row, row) == 8 for row in doubled)
    assert all(sum(column) == 0 for column in transpose(doubled))
    gram_twice = multiply(doubled, transpose(doubled))
    assert all(value % 4 == 0 for row in gram_twice for value in row)
    gram = [[value // 4 for value in row] for row in gram_twice]
    assert all(gram[i][j] in (-1, 0, 1) for i in range(count) for j in range(i))
    return [[5 * (i == j) - 2 * gram[i][j] for j in range(count)] for i in range(count)]


def check_marked_frame(frame):
    order = len(frame)
    assert all(row[i] == 1 and sum(row) == 5 for i, row in enumerate(frame))
    assert all(entry % 2 == (i == j)
               for i, row in enumerate(frame) for j, entry in enumerate(row))
    assert multiply(frame, transpose(frame)) == [
        [25 * (i == j) for j in range(order)] for i in range(order)
    ]


def weight_histogram_k5(doubled):
    code = set()
    for head in product(range(5), repeat=4):
        coefficients = head + (-sum(head) % 5,)
        code.add(tuple(dot(coefficients, vector) % 5 for vector in doubled))
    weights = [0] * 11
    for word in code:
        weights[sum(a != 0 for a in word)] += 1
    return weights


def combinations(vectors):
    return [tuple(sum(a * b for a, b in zip(coefficient, row)) % 5 for row in vectors)
            for coefficient in product(range(5), repeat=len(vectors[0]))]


def weight_histogram_e8(doubled):
    left = combinations([row[:4] for row in doubled])
    right = combinations([row[4:] for row in doubled])
    weights = [0] * 21
    for part_left in left:
        for part_right in right:
            weights[sum((a + b) % 5 != 0 for a, b in zip(part_left, part_right))] += 1
    return weights


def rank_mod_five(rows):
    matrix = [[entry % 5 for entry in row] for row in rows]
    rank = 0
    for j in range(len(matrix[0])):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][j]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        scale = pow(matrix[rank][j], -1, 5)
        for i in range(rank + 1, len(matrix)):
            multiple = matrix[i][j] * scale % 5
            matrix[i] = [(a - multiple * b) % 5 for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


def paley_factor(n):
    squares = {j*j % n for j in range(1, n)}

    def character(x):
        return 0 if x % n == 0 else (1 if x % n in squares else -1)

    order = sorted(squares)
    return [[character(y - x) - character(-y - x) for y in order] for x in order]


def check_repair(frame, n, expected_rank):
    integral = paley_factor(n)
    r = len(integral)
    width = len(frame)
    lift = [[frame[i][j] if i < width and j < width else 5 * (i == j)
             for j in range(r)] for i in range(r)]
    numerator = multiply(lift, integral)
    assert all(sum(row) == -5 for row in numerator)
    assert all(entry % 2 == (i == j)
               for i, row in enumerate(numerator) for j, entry in enumerate(row))
    assert multiply(transpose(numerator), numerator) == [
        [25 * (n * (i == j) - 2) for j in range(r)] for i in range(r)
    ]
    assert rank_mod_five(numerator) == expected_rank
    assert multiply(lift, numerator) == [[25 * value for value in row] for row in integral]


def main():
    k5 = k5_vectors()
    k5_matrix = marked_frame(k5)
    check_marked_frame(k5_matrix)
    assert rank_mod_five(k5_matrix) == 3
    k5_hist = weight_histogram_k5(k5)
    assert k5_hist == [1, 0, 0, 0, 0, 0, 0, 40, 60, 0, 24]
    check_repair(k5_matrix, 23, 3)

    e8 = json.loads(Path(__file__).with_name("e8_level5_vectors.json").read_text())
    assert len(e8) == 20 and all(len(row) == 8 for row in e8)
    for row in e8:
        assert sum(x % 2 for x in row) in (0, 8)
        assert sum(row) % 4 == 0
    assert multiply(transpose(e8), e8) == [[20 * (i == j) for j in range(8)] for i in range(8)]
    e8_matrix = marked_frame(e8)
    check_marked_frame(e8_matrix)
    assert rank_mod_five(e8_matrix) == 8
    reachable = {0}
    while True:
        extend = reachable | {i for i in range(20) if any(e8_matrix[i][j] for j in reachable)}
        if extend == reachable:
            break
        reachable = extend
    assert len(reachable) == 20
    e8_hist = weight_histogram_e8(e8)
    assert e8_hist == [
        1, 0, 0, 0, 0, 0, 0, 80, 128, 32, 1456, 3520, 9152, 17568, 43232, 66112,
        88320, 78208, 60544, 18176, 4096,
    ]
    check_repair(e8_matrix, 43, 8)
    print("LEVEL5-MARKED-FRAMES-PASS K5=10/rank3/dist7 E8=20/rank8/dist7")


if __name__ == "__main__":
    main()
