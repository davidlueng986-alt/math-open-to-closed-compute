"""Exact arithmetic controls for the outer-design large-prime symmetry bound."""

from itertools import combinations
from math import isqrt


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def fixed_count_candidates(t, p, cycles):
    points_fixed = 2*t - cycles*p
    limit = 2*(2*t - p)**2 // p**2
    lower = 0
    if points_fixed:
        lower = (2*t - 1) % p
    if points_fixed >= 2:
        lower = max(lower, (t - 1) % p)
    return tuple(f for f in range((4*t - 2) % p, limit + 1, p) if f >= lower)


def check_small_exception():
    t, p = 7, 5
    assert fixed_count_candidates(t, p, 1) == (6,)
    assert fixed_count_candidates(t, p, 2) == (6,)

    points_fixed = 2*t - p
    slots_per_fixed_block = t - p
    pair_residue = (t - 1) % p
    required = (points_fixed*pair_residue + slots_per_fixed_block - 1) // slots_per_fixed_block
    row_budget = (t - 1)*(t - 3)
    per_neighbor = (2*p - t)**2 - 1
    allowed = 1 + row_budget // per_neighbor
    assert (required, allowed) == (5, 4)

    sets = tuple(map(frozenset, combinations(range(4), 2)))
    assert all(any(len(a & b) != 1 for a, b in combinations(group, 2))
               for group in combinations(sets, 4))


def check_examples():
    survivors = []
    for t in range(5, 201, 2):
        for p in range(2*t // 3 + 1, t + 1):
            if is_prime(p) and any(fixed_count_candidates(t, p, c) for c in range(1, 2*t//p + 1)):
                survivors.append((t, p))
    assert survivors == [(7, 5)]
    check_small_exception()

    t = 599
    for p in range(t//2 + 1, t + 1):
        if is_prime(p):
            assert not any(fixed_count_candidates(t, p, c) for c in range(1, 2*t//p + 1))
    assert not is_prime(2*t - 1)
    assert fixed_count_candidates(65, 43, 3) == (0,)
    print("Outer design: large-prime fixed-block bounds and the (7,5) exception verified")
    print("t=599: no point automorphism of prime order above 599/2")


if __name__ == "__main__":
    check_examples()
