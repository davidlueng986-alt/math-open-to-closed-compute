"""Check T(13), T(19), two full controls, and the explicit power progressions."""

from itertools import product
from math import isqrt

from border4_2396 import pack, periodic
from verify import goethals_seidel, verify_orthogonal


T13 = (1, 2, 1, 2, 1, -2, 2, 3, 4, 4, -4, -4, -3)
T19 = (1, 1, 2, 1, 2, 2, 1, -2, -1, 2, 3, 3, 4, -4, -3, -4, 4, -3, 3)


def selection_words(entries):
    return tuple(tuple((1 if value > 0 else -1) if abs(value) == i else 0 for value in entries)
                 for i in range(1, 5))


def small_paley_blocks():
    prime, side = 19, 5
    multiplier = (2, 4)
    representatives = []
    seen = set()
    for label in range(prime + 1):
        if label in seen:
            continue
        first = (0, 1) if label == prime else (1, label)
        x, y = first
        for _ in range(side):
            point = y * pow(x, -1, prime) % prime if x else prime
            assert point not in seen
            seen.add(point)
            representatives.append((x, y))
            x, y = ((x*multiplier[0] - y*multiplier[1]) % prime,
                    (x*multiplier[1] + y*multiplier[0]) % prime)
        assert (x, y) == first
    assert seen == set(range(prime + 1))
    squares = {value*value % prime for value in range(1, prime)}
    rows = tuple(tuple(1 if i == j or (a*d - b*c) % prime in squares else -1
                       for j, (c, d) in enumerate(representatives))
                 for i, (a, b) in enumerate(representatives))
    assert verify_orthogonal(prime + 1, list(map(pack, rows))) == 190
    blocks = tuple(tuple(rows[i*side][j*side:(j + 1)*side] for j in range(4)) for i in range(4))
    for i, j, x, y in product(range(4), range(4), range(side), range(side)):
        assert rows[i*side + x][j*side + y] == blocks[i][j][(y - x) % side]
    return blocks


def verify_control(selectors, blocks):
    t_words = selection_words(selectors)
    length, side = len(selectors), len(blocks[0][0])
    size = length*side
    assert all(sum(abs(word[i]) for word in t_words) == 1 for i in range(length))
    assert periodic(t_words) == [length] + [0]*(length - 1)
    words = tuple(tuple(sum(t_words[i][x % length]*blocks[i][j][x % side] for i in range(4))
                        for x in range(size)) for j in range(4))
    assert all(set(word) == {-1, 1} for word in words)
    assert periodic(words) == [4*size] + [0]*(size - 1)
    pairs = verify_orthogonal(4*size, goethals_seidel(words))
    print(f"T{length} Paley product / order {4*size}: {pairs} exact column pairs")
    return pairs


def verify():
    blocks = small_paley_blocks()
    assert verify_control(T13, blocks) == 33670
    assert verify_control(T19, blocks) == 72010
    prime = 712051
    assert all(prime % d for d in range(2, isqrt(prime) + 1))
    assert pow(prime, 1434, 7644840) == 1
    n = 13 * (prime + 1)
    assert n == 9256676 and (n // 4) % 100590 == 599
    assert (4*n + 1) % 19 not in {x*x % 19 for x in range(19)}
    print("T13 Paley progression: prime 712051, period 1434, first multiplier 2314169 congruent to 599")
    second = 1355443
    assert all(second % d for d in range(2, isqrt(second) + 1))
    assert pow(second, 2868, 57537480) == 1
    size19 = 19*(second + 1)
    multiplier19 = size19 // 4
    assert multiplier19 == 6438359 and multiplier19 % 100590 == 599 and multiplier19 % 13 == 5
    assert (4*size19 + 1) % 11 not in {x*x % 11 for x in range(11)}
    print("T19 Paley progression: prime 1355443, period 2868, first multiplier 6438359 congruent to 5 modulo 13")


if __name__ == "__main__":
    verify()
