"""Replay the support census excluding a one-line paraunitary delay."""

from collections import Counter
from math import gcd, isqrt

from border4_2396_nested import nested_negative_words

N = 299
PRIME = 599
EXPECTED = {
    (True, 3): 1, (True, 6): 5, (True, 7): 18, (True, 8): 109,
    (True, 9): 32, (True, 10): 73, (True, 11): 45, (True, 12): 13,
    (False, 10): 2, (False, 11): 1,
}


def main():
    negative = nested_negative_words()
    assert (PRIME-1) % N == 0
    assert all(PRIME % d for d in range(2, isqrt(PRIME)+1))
    masks = tuple(sum((1 << r) for r, row in enumerate(negative) if not row[i])
                  for i in range(N))
    assert sum(mask & 1 != 0 for mask in masks) == 164
    assert gcd(164, N) == 1
    assert {0, 3, 4, 8} <= set(masks)
    empty = tuple(i for i, mask in enumerate(masks) if mask == 0)
    assert len(empty) == 59
    data = [set(masks[(a-i) % N] for i in empty) for a in range(N)]
    histogram = Counter((0 in item, len(item)) for item in data)
    assert histogram == EXPECTED
    exceptional = [(a, item) for a, item in enumerate(data)
                   if len(item) <= (5 if 0 in item else 9)]
    assert exceptional == [(269, {0, 2, 3})]
    assert [a for a, item in enumerate(data) if 0 not in item] == [18, 258, 294]
    assert 2 in data[18] and 2 in data[294] and {3, 4, 8} <= data[258]
    assert 4**3 < PRIME and {r*r+33 for r in (3, 5)} == {42, 58}
    assert all(x*x % PRIME != PRIME-1 for x in range(PRIME))
    print("Checked all 299 axes; only 269 passes the two-plane support capacity.")
    print("Axis 269 forces the first coordinate plane; its complement has no skew involution.")
    print("All axes also exclude a nonzero isotropic scalar reflection channel.")


if __name__ == "__main__":
    main()
