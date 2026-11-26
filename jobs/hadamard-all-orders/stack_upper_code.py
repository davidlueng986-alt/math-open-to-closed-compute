"""Replay upper reconstruction from a signed lower projection packet."""

from itertools import combinations

from stack_1197 import normalize
from stack_1197_four_channels import LOWER_OMITTED
from stack_1198_four_channel_mod32 import rebuild
from stack_1198_joint import dot
from stack_1198_mod5 import Basis
from stack_odd_t_auxiliary import signs, transpose
from verify import goethals_seidel, length_299_words, paley


def inverse_numerator(columns, projections):
    return tuple(sum((2 * (c >> row & 1) - 1) * p for c, p in zip(columns, projections, strict=True))
                 for row in range(len(columns)))


def dot_words(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True))


def check_small_control():
    # Same 12-order Paley control as stack_odd_t_auxiliary, with an all-odd boundary.
    normalized = signs(12, paley(11))
    columns = tuple((col[0], *(-entry for entry in col[1:])) for col in transpose(normalized))
    top = (0, 1, 2, 4)
    bottom = tuple(i for i in range(12) if i not in top)
    upper = tuple(tuple(col[i] for i in top) for col in columns)
    lower = tuple(tuple(col[i] for i in bottom) for col in columns)
    old = (0, 4, 6, 7)
    others = tuple(i for i in range(12) if i not in old)
    pair = next((u, x) for u, x in combinations(others, 2)
                if dot_words(upper[u], upper[x]) == dot_words(lower[u], lower[x]) == 0)
    u, x = pair
    projections = tuple(dot_words(lower[i], lower[x]) for i in old)
    assert all(q % 2 == 0 for q in projections)
    packet = tuple(-q // 2 for q in projections)
    assert all(q % 2 for q in packet) and sum(p*p for p in packet) == 4
    assert sum(dot_words(upper[i], upper[u]) * q for i, q in zip(old, packet, strict=True)) == 0
    numerator = tuple(dot_words(row, packet) for row in transpose(tuple(upper[i] for i in old)))
    assert all(z % 4 == 2 for z in numerator)
    assert tuple(z // 2 for z in numerator) == upper[x]



def quotient_matrix(raw, width):
    # Raw Goethals–Seidel columns are grouped by block and coordinate modulo width.
    assert 299 % width == 0
    compressed = []
    for col_block in range(4):
        for residue in range(width):
            possible = set()
            for col in range(residue, 299, width):
                word = raw[col_block * 299 + col]
                possible.add(tuple(sum(2 * (word >> (row_block * 299 + i) & 1) - 1
                                       for i in range(row, 299, width))
                                   for row_block in range(4) for row in range(width)))
            assert len(possible) == 1
            compressed.append(possible.pop())
    return compressed


def verify():
    check_small_control()
    old, second, lower, _ = rebuild()
    n, m = 1196, 1200
    mask = (1 << n) - 1
    u, v = old[-1] & mask, old[-1] >> n
    x, y = second & mask, second >> n
    data = tuple(dot(m, col >> n, y) for col in old[:-1])
    assert all(d % 4 == 0 for d in data)
    packet = tuple(-d // 4 for d in data)
    columns = [col & mask for col in old[:-1]]
    raw = goethals_seidel(length_299_words())
    assert columns == normalize(raw)
    assert dot(m, v, y) == 0 and dot(n, u, x) == 0
    omitted = tuple((dot(m, lower[j], v), dot(m, lower[j], y)) for j in LOWER_OMITTED)
    assert sum(q * q for _, q in omitted) == m*m - n*n
    assert sum(p * q for p, q in omitted) == 0
    assert sum(q * q for q in packet) == 299**2
    assert sum(dot(n, col, u) * q for col, q in zip(columns, packet, strict=True)) == 0
    predicted = inverse_numerator(columns, packet)
    assert all(p % 2 for p in predicted)
    assert sum(p * p for p in predicted) == n * 299**2
    assert tuple(sum(p % k != 0 for p in predicted) for k in (13, 23, 299)) == (1108, 1145, 1147)

    for width in (1, 13, 23):
        compressed = quotient_matrix(raw, width)
        for prime in (13, 23):
            basis = Basis(4 * width, prime)
            for column in compressed:
                pivot = basis.reduce(column)
                if pivot is not None:
                    basis.install(pivot)
            assert basis.rank == 2 * width
    print('Upper reconstruction: projected norms and parity verified; quotient ranks 2, 26, 46 over F13 and F23')
    print('E4352 pairing: upper reconstruction fails 1108 rows modulo 13 and 1145 rows modulo 23')


if __name__ == '__main__':
    verify()
