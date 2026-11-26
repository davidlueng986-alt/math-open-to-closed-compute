"""Check the Paley-II conference graph and sharp modulus-25 gap controls."""

from itertools import product

from stack_odd_t_residual import conference_positive_columns, paley_type_two
from verify import rows_from_columns


def sign(word, index):
    return 2 * (word >> index & 1) - 1


def verify_graph(prime):
    conference = conference_positive_columns(prime)
    size = len(conference)
    c = [[0 if i == j else sign(word, i) for j, word in enumerate(conference)] for i in range(size)]
    columns = paley_type_two(prime)
    for j, word in enumerate(columns):
        for i in range(size):
            base = j % size
            first, second = (c[i][base], int(i == base)) if j < size else (-int(i == base), c[i][base])
            assert sign(word, i) + sign(word, i + size) == 2 * first
            assert sign(word, i) - sign(word, i + size) == 2 * second
    assert all(sum(x*y for x, y in zip(a, b, strict=True)) == (prime if i == j else 0)
               for i, a in enumerate(c) for j, b in enumerate(c))
    return c, columns


def main():
    # The small Paley-II example realizes the F9 weight bound by full graph enumeration.
    small, _ = verify_graph(5)
    weights = []
    for left in product(range(3), repeat=len(small)):
        if not any(left):
            continue
        right = [sum(a*b for a, b in zip(row, left, strict=True)) % 3 for row in small]
        weights.append(sum(a != 0 or b != 0 for a, b in zip(left, right, strict=True)))
    assert len(weights) == 728 and min(weights) == 4

    c, columns = verify_graph(149)
    size = len(columns)
    assert size == 300 and len(c) == 150 and 12**2 < 149 <= 13**2
    assert [q for q in range(1, 150) if 3*q % 25 == 0 and (3*q // 25) % 2 == 0] == [50, 100]
    rows = rows_from_columns(size, columns)
    s = [(sign(rows[0], j) + sign(rows[1], j)) // 2 for j in range(size)]
    assert sum(value**2 for value in s) == 150
    ps = [sum(value * sign(row, j) for j, value in enumerate(s)) for row in rows]
    assert ps == [150, 150] + [0] * 298
    print('Paley-II H300: explicit 150-equation conference graph modulo 25; sharp squared residual gap 2400')
    print('Paley-II H12 control: all 728 nonzero ternary graph words, paired support minimum 4')


if __name__ == '__main__':
    main()
