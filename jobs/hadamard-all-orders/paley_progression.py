"""Check T(13), a full order-260 control, and the explicit power progression."""

from itertools import product
from math import isqrt

from border4_2396 import pack, periodic
from verify import goethals_seidel, verify_orthogonal


T13 = (1, 2, 1, 2, 1, -2, 2, 3, 4, 4, -4, -4, -3)


def t13_words():
    return tuple(tuple((1 if value > 0 else -1) if abs(value) == i else 0 for value in T13)
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


def verify():
    t13 = t13_words()
    assert all(sum(abs(word[i]) for word in t13) == 1 for i in range(13))
    assert periodic(t13) == [13] + [0]*12
    blocks = small_paley_blocks()
    words = tuple(tuple(sum(t13[i][x % 13]*blocks[i][j][x % 5] for i in range(4))
                        for x in range(65)) for j in range(4))
    assert all(set(word) == {-1, 1} for word in words)
    assert periodic(words) == [260] + [0]*64
    pairs = verify_orthogonal(260, goethals_seidel(words))
    assert pairs == 33670
    prime = 712051
    assert all(prime % d for d in range(2, isqrt(prime) + 1))
    assert pow(prime, 1434, 7644840) == 1
    n = 13 * (prime + 1)
    assert n == 9256676 and (n // 4) % 100590 == 599
    assert (4*n + 1) % 19 not in {x*x % 19 for x in range(19)}
    print(f"T13 Paley product / order 260: {pairs} exact column pairs")
    print("T13 Paley progression: prime 712051, period 1434, first multiplier 2314169 congruent to 599")


if __name__ == "__main__":
    verify()
