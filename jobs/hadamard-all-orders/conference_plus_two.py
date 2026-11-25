"""Replay the prime Paley conference input and exact order-2396 repair bounds."""

from itertools import combinations
from math import comb, isqrt


def conference_words(prime):
    """Pack C+I with the last index denoting the fixed Paley point."""
    assert prime % 4 == 1 and all(prime % d for d in range(2, isqrt(prime) + 1))
    squares = {value * value % prime for value in range(1, prime)}
    base = sum(1 << i for i in squares) | 1
    field_mask = (1 << prime) - 1
    return tuple((1 << prime) | (((base << d) | (base >> (prime - d))) & field_mask)
                 for d in range(prime)) + ((1 << (prime + 1)) - 1,)


def verify():
    prime = 2393
    side = prime + 1
    conference = conference_words(prime)
    for (i, left), (j, right) in combinations(enumerate(conference), 2):
        ij = (left >> j) & 1
        assert ij == (right >> i) & 1
        filled_dot = side - 2 * (left ^ right).bit_count()
        assert filled_dot == 2 * (2 * ij - 1)
    assert all(word >> i & 1 for i, word in enumerate(conference))
    untouched = 2 * (1 + isqrt(prime))
    numerator = side * side // 2 - 2 * side
    rank_rhs = (numerator + side - 3) // (side - 2)
    rank_edit = (rank_rhs - 1) // 2
    assert (side - untouched, rank_rhs, rank_edit) == (2296, 1196, 597)
    print(f"Paley conference / {side}: {comb(side, 2)} exact off-diagonal dots")
    print(f"order {side + 2}: {side - untouched} original rows and columns must change; edit rank at least {rank_edit}")


if __name__ == "__main__":
    verify()
