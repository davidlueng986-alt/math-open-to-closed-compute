"""Check the fixed-first rank obstruction and a C13-exact modulo-four source."""

from border4_2396 import periodic
from border4_2396_exact_negative import word
from border4_2396_nested import NEAR_C13, nested_negative_words, rank

N = 299
HALF = N // 2
AXIS = 269
X_SWITCH = (132, 17, 34, 257)
Y_SWITCH = (52, 15, 42, 55)
TARGET = [553] + [-46] * 12


def reflect(row):
    return tuple(row[(AXIS - i) % N] for i in range(N))


def incident(support, i):
    return sum((((i - d) % N in support) ^ ((i + d) % N in support)) << (d - 1)
               for d in range(1, HALF + 1))


def quotient(words):
    return periodic(tuple(tuple(sum(row[i::13]) for i in range(13)) for row in words))


def flip(row, positions):
    assert all(row[i] for i in positions)
    assert sum(row[i] for i in positions) == 0
    return tuple(-x if i in positions else x for i, x in enumerate(row))


def verify():
    t = nested_negative_words()
    s = tuple(map(word, NEAR_C13))
    p = {i for i, value in enumerate(s[2]) if value}
    a, b = s[2], reflect(s[3])
    assert len(p) == 130 and p == {i for i, value in enumerate(b) if value}
    assert tuple(map(sum, s)) == (0, 1, 0, 0)
    assert all((value + 2) % 8 == 0 for value in periodic(s)[1:])
    assert [v - u for v, u in zip(quotient(s), TARGET, strict=True)] == (
        [0, 0, 0, -8, 8, 0, 0, 0, 0, 8, -8, 0, 0]
    )

    # With the first pair fixed, these are the columns for changing the
    # relative sign mask at modulo four. The all-one mask is their dependency.
    relative_columns = [incident(p, i) for i in p]
    assert rank(relative_columns) == len(p) - 1 == 129

    x = tuple((u + v) // 2 for u, v in zip(a, b, strict=True))
    y = tuple((u - v) // 2 for u, v in zip(a, b, strict=True))
    assert sum(x) == sum(y) == 0
    supports = [{i for i, value in enumerate(row) if value} for row in (x, y)]
    assert supports[0] and supports[1] and supports[0].isdisjoint(supports[1])
    assert supports[0] | supports[1] == p
    # After fixing the mask, these are the modulo-eight switch columns
    # augmented by the two group-sum parity coordinates.
    simultaneous_columns = [incident(support, i) | (1 << (HALF + group))
                            for group, support in enumerate(supports) for i in support]
    assert rank(simultaneous_columns) == len(p) - 2 == 128

    xx, yy = flip(x, X_SWITCH), flip(y, Y_SWITCH)
    changed = s[:2] + (
        tuple(u + v for u, v in zip(xx, yy, strict=True)),
        reflect(tuple(u - v for u, v in zip(xx, yy, strict=True))),
    )
    for words in (s, changed):
        assert all(u * u + v * v == 1 for a, b in zip(words, t, strict=True)
                   for u, v in zip(a, b, strict=True))
        assert tuple(map(sum, words)) == (0, 1, 0, 0)
    assert quotient(changed) == TARGET
    positive_corr = periodic(changed)
    assert positive_corr[0] == 597
    assert all((value + 2) % 4 == 0 for value in positive_corr[1:])
    assert sum((value + 2) % 8 == 0 for value in positive_corr[1:]) == 170
    print("Fixed-first rank obstruction verified (129, 128).")
    print("Same first pair with exact C13: positive modulo four and 170 of 298 modulo-eight lags.")


if __name__ == "__main__":
    verify()
