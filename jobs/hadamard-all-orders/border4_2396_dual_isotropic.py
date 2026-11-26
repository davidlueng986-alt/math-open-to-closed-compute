"""Verify ternary norms whose quadratic term vanishes modulo eleven."""

from math import gcd
from itertools import combinations

from border4_2396 import periodic
from border4_2396_dual_quotient import (
    CHANGED_C13_MARGINS, LOW_AMPLITUDE_MOD16, MASKS, MORE_MOD16, dual_words,
)


def tensor(first, second):
    return tuple(tuple(row[i % 13]*second[i % 23] for i in range(299)) for row in first)


def check_norm(words, weight):
    assert sum(bool(v) for row in words for v in row) == weight
    assert all(sum(row[i::q]) == 0 for row in words for q in (13, 23) for i in range(q))
    assert all(set(row) <= {-1, 0, 1} for row in words)
    assert all(v % 11 == 0 for v in periodic(words))


def max_balanced_opposite(row):
    fibres = tuple(tuple(row[next(i for i in range(y, 299, 23) if i % 13 == x)]
                         for x in range(13)) for y in range(23))
    return max(2*min(sum(a == 1 and b == -1 for a, b in zip(left, right, strict=True)),
                     sum(a == -1 and b == 1 for a, b in zip(left, right, strict=True)))
               for left, right in combinations(fibres, 2))


def main():
    head = ((0, 0, 0, 1, -1, -1), (0, 1, -1, 0, -1, 1), (0, 1, -1, 1, 0, -1))
    first = tuple((0, *half, *(-v for v in reversed(half))) for half in head)
    assert periodic(first) == [22, -11] + [0]*10 + [-11]
    assert all(sum(row) == 0 for row in first)
    for values, weight, is_odd in (
        ({1: 1, 22: 1, 2: -1, 21: -1}, 88, True),
        ({0: 1, 1: -1}, 44, False),
    ):
        second = tuple(values.get(i, 0) for i in range(23))
        words = tensor(first, second)
        check_norm(words, weight)
        if is_odd:
            assert all(row[i] == -row[-i] for row in words for i in range(299))

    pair = tuple(tuple({'+': 1, '-': -1, '.': 0}[symbol] for symbol in row)
                 for row in ('+++-+-.--.+-.', '+++-++----+-.'))
    assert periodic(pair) == [22] + [0]*5 + [-11, -11] + [0]*5
    sharp = tensor(pair, (1, -1) + (0,)*21)
    assert tuple(sum(map(abs, row)) for row in sharp) == (20, 24)
    check_norm(sharp, 44)
    for masks, maxima in (
        (MASKS, (8, 10, 2, 4)),
        (MORE_MOD16, (6, 10, 2, 4)),
        (CHANGED_C13_MARGINS, (8, 10, 2, 4)),
        (LOW_AMPLITUDE_MOD16, (10, 10, 4, 4)),
    ):
        assert tuple(map(max_balanced_opposite, dual_words(masks))) == maxima
    assert 13*23 == 299 and (13-1)*(23-1) == 264 and gcd(299, 264) == 1
    print("Two and three ternary words realize quadratic cancellation at weight 44; odd triple at 88.")


if __name__ == "__main__":
    main()
