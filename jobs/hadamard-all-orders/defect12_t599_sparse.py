"""Verify the arithmetic and candidate counts for sparse interval comparators."""

from collections import Counter
from itertools import combinations_with_replacement
from math import comb, isqrt


PRIME = 599
MIDPOINT = PRIME // 2


def comparison_path(longer):
    """Get the uniquely forced interval reflection disagreements."""
    current = MIDPOINT
    seen = set()
    group_counts = [0, 0]
    while current not in (0, PRIME - 1):
        folded = min(current, PRIME - 1 - current)
        assert folded not in seen
        seen.add(folded)
        reflected = (longer - 1 - current) % PRIME
        assert reflected != current
        group = int(current >= longer)
        assert group == int(reflected >= longer)
        group_counts[group] += 1
        current = PRIME - 1 - reflected
    return len(seen), tuple(group_counts)


def placements(length, disagreements, minority):
    """Count bit supports inducing the specified reflection disagreements."""
    count = 0
    for center in range(1 + length % 2):
        remaining = minority - disagreements - center
        if remaining >= 0 and remaining % 2 == 0:
            count += comb(length // 2 - disagreements, remaining // 2)
    return count * (1 << disagreements)


def verify():
    squares = {i * i for i in range(isqrt(PRIME) + 1)}
    row_sum_pairs = Counter()
    for a, b in combinations_with_replacement(range(1, 6), 2):
        if a + b > 6:
            continue
        for u in range(a % 2, a + 1, 2):
            for v in range(b % 2, b + 1, 2):
                # A total of 599 has three odd squares and one even
                # square. Its even root is 2 modulo 4 up to sign.
                if any(x % 4 == 0 for x in (u, v)) or (u % 2 == v % 2 == 0):
                    continue
                for w2 in squares:
                    z2 = PRIME - u * u - v * v - w2
                    if z2 >= w2 and z2 in squares:
                        row_sum_pairs[a, b, u, v, isqrt(w2), isqrt(z2)] += 1
    assert row_sum_pairs == {(2, 3, 2, 3, 15, 19): 1}
    assert all(594 - w2 not in squares for w2 in squares)

    short_paths = {}
    for longer in range(MIDPOINT + 1, PRIME):
        length, counts = comparison_path(longer)
        distance = (MIDPOINT * pow(longer, -1, PRIME)) % PRIME
        assert length == min(distance, PRIME - distance)
        if length <= 5:
            short_paths[length] = (longer, counts)
    assert short_paths == {1: (300, (1, 0)), 2: (449, (1, 1)),
                           3: (499, (2, 1)), 4: (524, (3, 1)),
                           5: (539, (4, 1))}
    counts = {}
    for length, (longer, (left, right)) in short_paths.items():
        if length == 1:  # The alternating row sum excludes this split.
            continue
        shorter = PRIME - longer
        counts[longer, shorter] = sum(placements(longer, left, a) * placements(shorter, right, b)
                                      for a, b in ((2, 3), (3, 2)))
    assert counts == {(449, 150): 296, (499, 100): 392, (524, 75): 16, (539, 60): 0}
    print("t=599 exact sparse interval comparators: no balanced split; 704 candidate partitions across three other splits")


if __name__ == "__main__":
    verify()
