"""Check the mixed-shift parity obstruction on two exact selector families."""

from itertools import product
from operator import xor

from border4_2396 import periodic
from paley_progression import T13, T19, selection_words


def verify():
    for seed in (T13, T19):
        length = len(seed)
        assert periodic(selection_words(seed)) == [length] + [0]*(length - 1)
    first = tuple(abs(value) - 1 for value in T13)
    second = tuple(abs(value) - 1 for value in T19)
    n, m = len(first), len(second)
    shifts = tuple(product(range(1, n), range(1, m)))
    for combine in (xor, lambda a, b: (a + b) % 4):
        labels = tuple(tuple(combine(a, b) for b in second) for a in first)
        for a, b in shifts:
            overlaps = sum(labels[i][j] == labels[(i + a) % n][(j + b) % m]
                           for i, j in product(range(n), range(m)))
            assert overlaps % 2 == 1
    print(f"T13 x T19: {len(shifts)} mixed shifts are odd under each four-label group law")


if __name__ == "__main__":
    verify()
