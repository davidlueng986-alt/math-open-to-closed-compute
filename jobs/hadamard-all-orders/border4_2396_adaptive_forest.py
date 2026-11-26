"""Replay the bounded mixed-radix circulation gate and its physical source."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import log2

from border4_2396 import periodic
from border4_2396_dual_changed_support import cyclic_tail_negative, positive_words
from border4_2396_dual_joint_geometry import change_second_head, raw_stats
from border4_2396_dual_mod5_forest import residual
from border4_2396_nested import nested_negative_words

N = 299
POSITIONS = {(i % 13, i % 23): i for i in range(N)}
EDGES = tuple(product(range(7), range(12)))[1:]
GEOMETRY_MASKS = (
    0x104B202050DA46603203D00D2625002C11048080182F0594100060451011D82802A04307A00,
    0x780141BC1000E2063711618D200020812819020A952410C40D200C3040AA28D3240A14D13,
    0x2225801820010080A00D0000A20180B7390484B00C0C05082C080100A40484A0000445102C0,
    0x680901200D188100C10001804D19126F5804032080010120440C80288C002000200CA1288,
)

GEOMETRY0_MASKS = (
    0x306E2008D412044032838005002402031900CC80582581805CA025043051A02883906307608,
    0x42C0241AA1841EA061491418A008203C00C188202800491E60D24881201A2044266CA16E12,
    0x22180102000009020010110020C81F64F14452004048418A8084110A404C420301445100C0,
    0x6101810049180128401000A00109668BF80402280C050120000D80A84409010024088308C,
)

def lags(edge):
    x, y = edge
    first = POSITIONS[x, y]
    return (first, POSITIONS[x, -y % 23]) if x and y else (first,)


def forest(edges):
    roots = list(range(19))

    def root(i):
        while roots[i] != i:
            i = roots[i]
        return i

    result = set()
    for x, y in edges:
        a, b = root(x), root(7 + y)
        if a != b:
            roots[a] = b
            result.add((x, y))
    return result


def inside_modulus(bounds):
    if len(bounds) == 1 or min(bounds) == 0:
        return 1
    b = min(bounds)
    return b + 1 + int(b % 2 == 1)


def outside_modulus(bounds):
    return (bounds[0] + 1) * (bounds[1] + 1) if len(bounds) == 2 else bounds[0] + 1


def gate(e, bounds):
    """Return the exact weighted-tree gate and the count of failed residues."""
    assert e[0] == 0 and all(e[i] == e[-i % N] for i in range(N))
    assert all(sum(e[i::q]) == 0 for q in (13, 23) for i in range(q))
    assert all(abs(v) <= b for v, b in zip(e, bounds, strict=True))
    box = {edge: tuple(bounds[i] for i in lags(edge)) for edge in EDGES}
    high = sorted(edge for edge in EDGES if max(box[edge]) >= 5)
    assert len(forest(high)) == len(high)
    in_mod = {edge: inside_modulus(cap) for edge, cap in box.items()}
    out_mod = {edge: outside_modulus(cap) for edge, cap in box.items()}
    ranked = sorted(EDGES, key=lambda edge: (Fraction(out_mod[edge], in_mod[edge]), edge),
                    reverse=True)
    tree = forest((*high, *(edge for edge in ranked if edge not in high)))
    assert len(tree) == 18 and set(high) <= tree

    aggregate = {}
    histogram = Counter()
    failures = 0
    for edge, cap in box.items():
        v = tuple(e[i] for i in lags(edge))
        aggregate[edge] = sum(v)
        if edge in tree:
            modulus = in_mod[edge]
            value = v[0] - v[-1]
        else:
            modulus = out_mod[edge]
            value = v[0] + (cap[0] + 1) * v[1] if len(v) == 2 else v[0]
        if modulus > 1:
            histogram[modulus] += 1
            failures += value % modulus != 0

    assert all(sum(v for (x, _), v in aggregate.items() if x == i) == 0 for i in range(7))
    assert all(sum(v for (_, y), v in aggregate.items() if y == i) == 0 for i in range(12))
    if not failures:
        assert not any(aggregate[edge] for edge in EDGES if edge not in tree)
        assert not any(aggregate.values())
        assert not any(e)
    return histogram, failures


def check_local_alphabets():
    for a, b in product(range(7), repeat=2):
        m = outside_modulus((a, b))
        points = product(range(-a, a + 1), range(-b, b + 1))
        assert all((i + (a + 1) * j) % m or (i, j) == (0, 0) for i, j in points)


def magnitude_graphs(bounds, prime):
    """Group allowed aggregate magnitudes after division by the even modulus."""
    assert all(0 <= value <= 6 for value in bounds)
    graphs = {}
    for edge in EDGES:
        cap = tuple(bounds[i] for i in lags(edge))
        if len(cap) == 1:
            values = range(prime, cap[0] + 1, prime)
        else:
            a, b = cap
            values = {
                u + v for u, v in product(range(-a, a + 1), range(-b, b + 1))
                if (u - v) % 7 == 0 and u + v > 0 and (u + v) % prime == 0
            }
        for value in values:
            weight = value // prime
            assert weight in (1, 2, 4)
            graphs.setdefault(weight, set()).add(edge)
    return graphs


def check_magnitude_source(negative):
    positive = positive_words(negative, GEOMETRY0_MASKS)
    assert raw_stats(positive, negative) == (285, 89, 48, 268800, 145, 89)
    e = residual(positive)
    literal = tuple(map(abs, e))
    graphs = magnitude_graphs(literal, 3)
    assert {w: len(g) for w, g in graphs.items()} == {1: 13, 2: 6}
    assert all(len(forest(sorted(g))) == len(g) for g in graphs.values())
    odd_failures = sum((e[i] - e[j]) % 7 != 0
                       for edge in EDGES if all(edge) for i, j in (lags(edge),))
    even_failures = sum((e[i] + e[j]) % 3 != 0
                        for edge in EDGES if all(edge) and edge != (6, 11)
                        for i, j in (lags(edge),))
    assert (odd_failures, even_failures) == (58, 46)

    loose = [abs(v) if abs(v) >= 5 else 4 for v in e]
    for d in lags((2, 1)):
        loose[d] = loose[-d % N] = 5
    graphs = magnitude_graphs(loose, 5)
    assert {w: len(g) for w, g in graphs.items()} == {1: 5, 2: 2}
    assert all(len(forest(sorted(g))) == len(g) for g in graphs.values())
    union = set.union(*graphs.values())
    assert len(union) == 7 and len(forest(sorted(union))) == 6
    print("separate magnitude forests: mod3 edges 13 and 6; mod5 union has one cycle")


def main():
    check_local_alphabets()
    negative = change_second_head(cyclic_tail_negative(nested_negative_words()))
    assert periodic(negative) == [599] + [0] * (N - 1)
    positive = positive_words(negative, GEOMETRY_MASKS)
    assert raw_stats(positive, negative) == (333, 101, 48, 268800, 165, 101)
    e = residual(positive)
    assert sum(any(abs(e[i]) >= 5 for i in lags(k)) for k in EDGES) == 11
    models = (
        ("uniform", tuple(6 if abs(x) >= 5 else 4 for x in e),
         {5: 31, 25: 50}, 71),
        ("rounded", tuple(max(2, 2 * ((abs(x) + 1) // 2)) for x in e),
         {3: 25, 5: 6, 9: 23, 15: 19, 25: 8}, 71),
        ("preserved zeros", tuple(2 * ((abs(x) + 1) // 2) for x in e),
         {3: 26, 5: 10, 9: 12, 15: 15, 25: 8}, 69),
    )
    check_magnitude_source(negative)
    for label, bounds, expected_moduli, expected_failures in models:
        histogram, failures = gate(e, bounds)
        assert (histogram, failures) == (expected_moduli, expected_failures)
        entropy = sum(n * log2(m) for m, n in histogram.items())
        print(label, "checks", sum(histogram.values()), "failed", failures,
              "log2 alphabet product", round(entropy, 4))


if __name__ == "__main__":
    main()
