"""Check the order-2396 D12+ shadow model modulo 16 using exact arithmetic."""

from collections import defaultdict
from itertools import combinations


ORDER = 2396
LENGTH = ORDER // 4
SIZE = 12
TETRAD = (898, 899, 2096, 2097)
RESIDUAL_COLUMNS = (0, 1, 150, 300, 898, 1048, 1198, 1497, 1647, 1796, 2096, 2246)
NORMALIZING_COLUMN = 149
MINOR_ROWS = (0, 1, 4, 3, 301, 151, 149, 154, 302, 150, 450, 451)


def word(bits):
    return sum(bit << i for i, bit in enumerate(bits))


def bit(value, position):
    return (value >> position) & 1


def dot(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True))


def eliahou_kervaire_rows():
    """Theorem 3.2.2 and array (3), with reversal j -> -j modulo LENGTH."""
    r = (LENGTH - 3) // 4
    assert LENGTH == 4 * r + 3 and r % 2 == 1
    tail = (-1, 1) * ((r - 1) // 2)
    h = (1,) * (r - 1) + (-1, 1, 1) + tail
    k = (-1,) * (r - 1) + (1, -1, 1) + tail

    def negative_sharp(sequence):
        return tuple(-a * (-1)**i for i, a in reversed(list(enumerate(sequence))))

    h_sharp = negative_sharp(h)
    k_sharp = negative_sharp(k)
    sequences = (h + (1,) + h_sharp, h + (1,) + k_sharp,
                 k + (1,) + h_sharp, k + (-1,) + k_sharp)
    # A circulant, its product with reversal, and its transpose times reversal.
    blocks = (((0, 1, -1, 1), (1, -1, -1, -1), (2, -1, -1, -1), (3, -1, -1, -1)),
              ((1, -1, -1, 1), (0, 1, -1, 1), (3, 1, 1, -1), (2, 1, 1, 1)),
              ((2, -1, -1, 1), (3, 1, 1, 1), (0, 1, -1, 1), (1, 1, 1, -1)),
              ((3, -1, -1, 1), (2, 1, 1, -1), (1, 1, 1, 1), (0, 1, -1, 1)))
    return [word(sign * sequences[sequence][(j_sign * j + i_sign * i) % LENGTH] < 0
                 for sequence, j_sign, i_sign, sign in group for j in range(LENGTH))
            for group in blocks for i in range(LENGTH)]


def determinant(rows):
    """Bareiss elimination on the small integer minor."""
    matrix = [list(r) for r in rows]
    divisor = sign = 1
    for j in range(len(matrix) - 1):
        pivot_index = next((i for i in range(j, len(matrix)) if matrix[i][j]), None)
        if pivot_index is None:
            return 0
        if pivot_index != j:
            matrix[j], matrix[pivot_index] = matrix[pivot_index], matrix[j]
            sign = -sign
        pivot = matrix[j][j]
        for i in range(j + 1, len(matrix)):
            for k in range(j + 1, len(matrix)):
                numerator = pivot * matrix[i][k] - matrix[i][j] * matrix[j][k]
                matrix[i][k], remainder = divmod(numerator, divisor)
                assert remainder == 0
            matrix[i][j] = 0
        divisor = pivot
    return sign * matrix[-1][-1]


def reflect():
    source = eliahou_kervaire_rows()
    assert all((source[i] ^ source[j]).bit_count() == ORDER // 2 for i, j in combinations(TETRAD, 2))
    panel = [word(bit(row, j) for row in source) for j in (*RESIDUAL_COLUMNS, NORMALIZING_COLUMN)]
    assert all((a ^ b).bit_count() == ORDER // 2 for a, b in combinations(panel, 2))
    ones = (1 << ORDER) - 1
    rows = [row ^ (ones if bit(row, NORMALIZING_COLUMN) else 0) for row in source]
    product = 0
    for i in TETRAD:
        product ^= rows[i]
    assert product == word(int(j in RESIDUAL_COLUMNS) for j in range(ORDER))

    kept = [NORMALIZING_COLUMN, *(j for j in range(ORDER)
                                  if j != NORMALIZING_COLUMN and j not in RESIDUAL_COLUMNS)]
    sign_rows = [word(bit(row, j) for j in kept) for row in rows]
    residual = [[1 - 2 * bit(row, j) for j in RESIDUAL_COLUMNS] for row in rows]
    half_sums = [2 - sum(bit(rows[i], j) for i in TETRAD) for j in range(ORDER)]
    for i in TETRAD:
        reflected = [half_sum - (1 - 2 * bit(rows[i], j)) for j, half_sum in enumerate(half_sums)]
        assert all(reflected[j] in (-1, 1) for j in kept)
        sign_rows[i] = word(reflected[j] == -1 for j in kept)
        residual[i] = [reflected[j] for j in RESIDUAL_COLUMNS]
    for row in residual:
        row[0] *= -1

    assert determinant([residual[i] for i in MINOR_ROWS]) == 16384
    for i, row in enumerate(residual):
        assert all(value % 2 == int(i not in TETRAD) for value in row)
    reference = TETRAD[0]
    ordered_rows = [reference, *(i for i in range(ORDER) if i != reference)]
    orientation = sign_rows[reference]
    return [sign_rows[i] ^ orientation for i in ordered_rows], [tuple(residual[i]) for i in ordered_rows]


def doubled_basis():
    yield (1,) * SIZE
    for i in range(1, SIZE - 1):
        yield tuple(2 if j == i else -2 if j == i + 1 else 0 for j in range(SIZE))
    yield (0,) * (SIZE - 2) + (2, 2)


def verify():
    signs, residual = reflect()
    assert len(signs) == len(residual) == ORDER and signs[0] == 0
    assert all(sign % 2 == 0 for sign in signs)
    for sign, row in zip(signs, residual, strict=True):
        assert dot(row, row) == SIZE and sum(row) % 4 == 2
        assert sign.bit_count() % 2 == row[0] % 2
    residual_columns = list(zip(*residual, strict=True))
    assert all(sum(r) == 0 for r in residual_columns)
    assert all(dot(r, s) == ORDER * int(i == j)
               for i, r in enumerate(residual_columns) for j, s in enumerate(residual_columns))

    # Verify A^T A and the weighted row Gram modulo 16.
    width = ORDER - SIZE
    columns = [word(bit(row, j) for row in signs) for j in range(width)]
    assert all((a ^ b).bit_count() % 8 == (ORDER // 2) % 8 for a, b in combinations(columns, 2))
    assert ORDER - 2 * (columns[0] ^ columns[2]).bit_count() == 32
    distinct = set(residual)
    shifts = {(r, s): (width + dot(r, s)) % 16 for r in distinct for s in distinct}
    for i, (row, r) in enumerate(zip(signs, residual, strict=True)):
        for j in range(i):
            assert 2 * (row ^ signs[j]).bit_count() % 16 == shifts[r, residual[j]]

    # Verify C^T A, where C has entries 2 <rho_i,b> in an integral U basis.
    for b in doubled_basis():
        masks = defaultdict(int)
        for i, r in enumerate(residual):
            value = dot(b, r)
            assert value % 2 == 0
            masks[(value // 2) % 8] |= 1 << i
        assert all(sum(value * (mask & col).bit_count() for value, mask in masks.items()) % 8 == 0
                   for col in columns)

    print("n=2396: exact zero-sum D12+ shadow frame, both Gram identities modulo 16")


if __name__ == "__main__":
    verify()
