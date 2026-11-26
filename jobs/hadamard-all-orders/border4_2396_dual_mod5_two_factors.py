"""Verify an integer residual criterion omitting one degree-44 factor modulo five."""

from itertools import product

from border4_2396_dual_mod5_forest import FACTORS_5, check_factors, forest, residual
from border4_2396_dual_peak48 import LOW_ENERGY_MASKS
from border4_2396_dual_quotient import dual_words, endpoints
from border4_2396_primitive_field import remainder


NARROW = {21: (0, 1), 145: (-1, 0), 2: (0, 3), 125: (0, 1), 7: (-2, 0)}


def coefficient_column(lag):
    left, right = endpoints(lag)
    vector = [0]*19
    vector[left], vector[right] = 1, 4
    polynomial = tuple(int(j in (lag, 299-lag)) for j in range(299))
    for factor in FACTORS_5[1:]:
        vector.extend(remainder(polynomial, factor, 5))
    return vector


def kernel(columns):
    pivot_rows = {}
    relations = []
    for j, column in enumerate(columns):
        reduced = list(column)
        relation = [0]*len(columns)
        relation[j] = 1
        for i in range(len(reduced)):
            entry = reduced[i]
            if not entry:
                continue
            if i in pivot_rows:
                pivot, previous = pivot_rows[i]
                reduced = [(x-entry*y) % 5 for x, y in zip(reduced, pivot, strict=True)]
                relation = [(x-entry*y) % 5 for x, y in zip(relation, previous, strict=True)]
            else:
                inverse = pow(entry, -1, 5)
                pivot_rows[i] = ([inverse*x % 5 for x in reduced],
                                 [inverse*x % 5 for x in relation])
                break
        else:
            relations.append(relation)
    assert len(pivot_rows) + len(relations) == len(columns)
    assert all(sum(a*b for a, b in zip(row, v, strict=True)) % 5 == 0
               for row in zip(*columns, strict=True) for v in relations)
    return relations


def components(high):
    roots = list(range(19))

    def root(i):
        while roots[i] != i:
            i = roots[i]
        return i

    for lag in high:
        a, b = map(root, endpoints(lag))
        assert a != b
        roots[a] = b
    return tuple(map(root, range(19)))


def combinations(basis, positions):
    return [tuple(sum(a*v[i] for a, v in zip(weights, basis, strict=True)) % 5
                  for i in positions)
            for weights in product(range(5), repeat=len(basis))]


def verify():
    check_factors()
    original = residual(dual_words(LOW_ENERGY_MASKS))
    active = tuple(d for d in range(1, 150) if original[d])
    high = tuple(d for d in active if abs(original[d]) >= 5)
    assert len(active) == 108 and high == (48, 51, 53, 79, 83, 86, 99, 147)
    assert forest(high) == (high, ())
    lows = tuple(d for d in active if d not in high)
    assert len(lows) == 100
    intervals = tuple(min(-2, original[d]) if original[d] <= 2 else original[d]-4 for d in lows)
    assert all(l <= min(0, original[d]) <= max(0, original[d]) <= l+4
               for d, l in zip(lows, intervals, strict=True))
    assert all(a <= min(0, original[d]) <= max(0, original[d]) <= b
               for d, (a, b) in NARROW.items())

    rel = kernel([coefficient_column(d) for d in active])
    assert len(rel) == 7
    positions = tuple(active.index(d) for d in lows)
    left, right = combinations(rel[:3], positions), combinations(rel[3:], positions)
    assert len(left)*len(right) == 78_125
    roots = components(high)
    cuts = []
    for j, d in enumerate(lows):
        a, b = (roots[i] for i in endpoints(d))
        if a != b:
            cuts.append((j, a, b))
    narrow = tuple((lows.index(d), a, b) for d, (a, b) in NARROW.items())

    balanced = 0
    survivors = []
    for first in left:
        for second in right:
            values = [(a+b-offset) % 5 + offset
                      for a, b, offset in zip(first, second, intervals, strict=True)]
            net = [0]*19
            for j, a, b in cuts:
                net[a] += values[j]
                net[b] -= values[j]
            if any(net):
                continue
            balanced += 1
            if all(a <= values[j] <= b for j, a, b in narrow):
                survivors.append(values)
    assert balanced == 585 and survivors == [[0]*len(lows)]
    assert tuple(sum(bool(v) for v in remainder(original, f, 5))
                 for f in FACTORS_5[1:]) == (35, 32)
    print("Two mod5 factors: 78125 residue vectors, 585 integer component balances, only zero survives")


if __name__ == "__main__":
    verify()
