"""Check positive single-parity and mixed controls for the odd-t stacked lift."""
from collections import Counter
from itertools import combinations, product

from verify import paley


def transpose(matrix):
    return tuple(zip(*matrix, strict=True))


def dot(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True))


def multiply(left, right):
    columns = transpose(right)
    return tuple(tuple(dot(row, col) for col in columns) for row in left)


def orthogonal(columns, norm):
    return (all(dot(col, col) == norm for col in columns)
            and all(dot(a, b) == 0 for a, b in combinations(columns, 2)))


def signs(order, packed_columns):
    return tuple(tuple(2 * (col >> i & 1) - 1 for i in range(order)) for col in packed_columns)


def sylvester(order):
    return tuple(tuple((-1)**((i & j).bit_count() % 2) for j in range(order)) for i in range(order))


def canonical(word):
    sign = 1 if next(entry for entry in word if entry) > 0 else -1
    return tuple(sign * value for value in word)


def ternary_span(columns):
    span = {(0,) * len(columns[0])}
    for column in columns:
        additions = {tuple((a + factor*b) % 3 for a, b in zip(word, column, strict=True))
                     for word in span for factor in (1, 2)}
        span.update(additions)
    return span


def numerator(a, b, d, k):
    ba = multiply(transpose(b), a)
    dk = multiply(transpose(d), k)
    return tuple(tuple(-value for value in row) + omitted for row, omitted in zip(ba, dk, strict=True))


def exact_kernel(a, b, d, k):
    n, m, order = len(a), len(b) + len(d), len(a) + len(b) + len(d)
    assert m == n + 4 and order % 8 == 4
    assert orthogonal(a, n) and orthogonal(b + d, m) and orthogonal(k, order)
    w = numerator(a, b, d, k)
    lifts = {}
    for s in product((1, -1), repeat=m):
        values = tuple(dot(row, s) for row in w)
        assert dot(values, values) == m**3
        if all(value % (2*m) == m for value in values):
            y = tuple(value // m for value in values)
            assert all(abs(value) == 1 for value in y)
            lifts[s] = s[:n] + y
    assert len(lifts) == 2*m
    first = next(iter(lifts))
    homogeneous = set()
    for z in product((0, 1), repeat=m):
        difference = tuple(s * bit for s, bit in zip(first, z, strict=True))
        if all(dot(row, difference) % m == 0 for row in w):
            assert sum(z) in (0, m//2, m)
            homogeneous.add(tuple(s - 2 * value for s, value in zip(first, difference, strict=True)))
    assert homogeneous == lifts.keys()
    independent = [s for s in lifts if s[0] == 1]
    assert orthogonal(independent, m)
    old = [upper + lower for upper, lower in zip(a, b, strict=True)]
    future = [lifts[s] for s in independent]
    assert orthogonal(old + future, order)
    counts = Counter()
    for col in future:
        z = tuple(dot(d_col, col[n:]) // 2 for d_col in d)
        assert len({entry % 2 for entry in z}) == 1
        counts[canonical(z)] += 1
    return lifts, counts


def single_odd_control():
    normalized = signs(12, paley(11))
    # Transpose the normalized Paley matrix and reverse each finite row.
    cols = tuple((col[0], *(-entry for entry in col[1:])) for col in transpose(normalized))
    assert orthogonal(cols, 12)
    top = (0, 1, 2, 4)
    bottom = tuple(i for i in range(12) if i not in top)
    old = (0, 4, 6, 7)
    future = tuple(j for j in range(12) if j not in old)
    upper = tuple(tuple(col[i] for i in top) for col in cols)
    lower = tuple(tuple(col[i] for i in bottom) for col in cols)
    a, b = tuple(upper[j] for j in old), tuple(lower[j] for j in old)
    d = ((1, 1, -1, 1, -1, -1, 1, -1), (1, 1, -1, -1, -1, 1, -1, 1),
         (1, -1, -1, 1, 1, -1, -1, 1), (1, -1, -1, -1, 1, 1, 1, -1))
    assert all(sum(value == -1 for value in row) % 2 == 0 for row in transpose(d))
    z = tuple(tuple(dot(destination, lower[j]) // 2 for destination in d) for j in future)
    assert all(value % 2 for projection in z for value in projection)
    e = tuple(sorted(set(map(canonical, z))))
    assert len(e) == 4 and orthogonal(e, 12)
    r = sylvester(4)
    k = tuple(tuple(value // 2 for value in row) for row in multiply(transpose(e), transpose(r)))
    lifts, counts = exact_kernel(a, b, d, k)
    assert len(counts) == 4 and set(counts.values()) == {2}
    for j, projection in zip(future, z, strict=True):
        f = tuple(sum(entry * dot(direction, projection) // 12 for entry, direction in zip(row, e, strict=True))
                  for row in r)
        assert lifts[upper[j] + f] == upper[j] + lower[j]
    print('odd-t auxiliary control t=3: all-odd closed omissions; 16 binary solutions')


def mixed_control():
    a = sylvester(8)
    lower = signs(12, paley(11))
    order = (8, 6, 10, 2, 0, 3, 5, 1, 11, 4, 9, 7)
    orientation = (-1, 1, -1, -1, 1, -1, 1, 1, 1, 1, 1, -1)
    selected = tuple(tuple(s * entry for entry in lower[j]) for j, s in zip(order, orientation, strict=True))
    k = ((1, 1, 3, 3), (-1, 1, -3, 3), (-3, 3, 1, -1), (-3, -3, 1, 1))
    lifts, counts = exact_kernel(a, selected[:8], selected[8:], k)
    even = [count for direction, count in counts.items() if direction[0] % 2 == 0]
    odd = [count for direction, count in counts.items() if direction[0] % 2 == 1]
    assert len(even) == len(odd) == 4 and len(set(even)) == len(set(odd)) == 1
    assert even[0] + odd[0] == 3
    transformed = tuple(tuple(-dot(column, s[:8]) for column in a)
                        + tuple(dot(row, s[8:]) for row in k)
                        for s in lifts if s[0] == 1)
    target_code = ternary_span(transpose(selected))
    assert len(target_code) == 729 and ternary_span(transformed) == target_code
    print('odd-t auxiliary control t=5: mixed directions; 24 binary solutions construct H20')
    print('odd-t auxiliary control t=5: exact ternary code equality, 729 words')


if __name__ == '__main__':
    single_odd_control()
    mixed_control()
