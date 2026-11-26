"""Verify ternary norms whose quadratic term vanishes modulo eleven."""

from math import gcd
from border4_2396 import periodic


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
        words = tuple(tuple(row[i % 13]*second[i % 23] for i in range(299)) for row in first)
        assert sum(bool(v) for row in words for v in row) == weight
        assert all(sum(row[i::q]) == 0 for row in words for q in (13, 23) for i in range(q))
        assert all(set(row) <= {-1, 0, 1} for row in words)
        assert all(v % 11 == 0 for v in periodic(words))
        if is_odd:
            assert all(row[i] == -row[-i] for row in words for i in range(299))
    assert 13*23 == 299 and (13-1)*(23-1) == 264 and gcd(299, 264) == 1
    print("Three-word ternary quadratic cancellation at weights 44 and 88.")


if __name__ == "__main__":
    main()
