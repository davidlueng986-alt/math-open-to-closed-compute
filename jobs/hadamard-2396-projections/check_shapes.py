"""Enumerate the invariant 133-point shapes independently using scalar correlations."""

import itertools
import math
from collections import Counter, defaultdict
from functools import cache


def orbit(value, prime):
    residue = value % prime
    if residue == 0:
        return 0
    return 1 if any(j*j % prime == residue for j in range(1, prime)) else 2


@cache
def prime_margins(prime):
    weight = (prime - 1) // 2
    total = 2396 - 2*(1197 // prime)
    limit = math.isqrt(total)
    odd_values = range((-limit) | 1, limit + 1, 2)
    by_norm = defaultdict(list)
    for square, nonsquare in itertools.product(odd_values, repeat=2):
        zero = 1 - weight*(square + nonsquare)
        norm = zero*zero + weight*(square*square + nonsquare*nonsquare)
        if norm < total:
            by_norm[norm].append((zero, square, nonsquare))
    return [(a, b) for norm, rows in by_norm.items() for a in rows if a[1] >= a[2]
            for b in by_norm.get(total - norm, ())]


@cache
def rows_over_19(total):
    return [row for row in itertools.product(range(-9, 10, 2), repeat=3)
            if row[0] + 9*(row[1] + row[2]) == total]


classes = [3*orbit(j, 7) + orbit(j, 19) for j in range(133)]
# Reflection and the independent square actions cover all shifts via these representatives.
products = [Counter((classes[i], classes[(i+s) % 133]) for i in range(133))
            for s in (0, 1, 2, 7, 19)]


@cache
def orbit_tables(seven, nineteen):
    by_correlation = defaultdict(list)
    for x, y, z in itertools.product(*(rows_over_19(total) for total in seven)):
        if tuple(x[i] + 3*(y[i] + z[i]) for i in range(3)) != nineteen:
            continue
        cells = x + y + z
        key = tuple(sum(count*cells[i]*cells[j] for (i, j), count in weights.items())
                    for weights in products)
        if key[0] <= 2378:
            by_correlation[key].append(cells)
    return by_correlation


def direct_shapes():
    found = set()
    for a, b in prime_margins(7):
        for c, d in prime_margins(19):
            left, right = orbit_tables(a, c), orbit_tables(b, d)
            for key, rows in left.items():
                complement = tuple(goal - value for goal, value in zip((2378, -18, -18, -18, -18), key))
                found.update(itertools.product(rows, right.get(complement, ())))
    return sorted(found)


if __name__ == "__main__":
    from shapes import shapes

    direct = direct_shapes()
    if direct != shapes():
        raise ValueError("scalar orbit sums and Gauss sums found different shapes")
    print(f"{len(direct)} normalized 133-point shapes, identical by both enumerations")
