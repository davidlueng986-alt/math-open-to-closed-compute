"""Check an exact maximal 28-by-16 partial Hadamard with D12+ residual lattice."""

from fractions import Fraction
from math import prod


ORDER = 28
TETRAD = (0, 1, 2, 4)
RESIDUAL_COLUMNS = (1, 4, 6, 11, 13, 14, 15, 16, 22, 24, 25, 26)
MINOR_ROWS = (0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13)


def digits(value):
    return value % 3, value // 3 % 3, value // 9


def encode(coefficients):
    return sum(value % 3 * 3**i for i, value in enumerate(coefficients))


def subtract(x, y):
    return encode(a - b for a, b in zip(digits(x), digits(y), strict=True))


def multiply(x, y):
    """Multiply in F_3[X]/(X^3-X-1), with coefficientwise base-3 encoding."""
    coefficients = [0] * 5
    for i, a in enumerate(digits(x)):
        for j, b in enumerate(digits(y)):
            coefficients[i + j] += a * b
    for i in (4, 3):
        coefficients[i - 2] += coefficients[i]
        coefficients[i - 3] += coefficients[i]
    return encode(coefficients[:3])


def dot(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True))


def determinant(rows):
    matrix = [[Fraction(value) for value in row] for row in rows]
    result = Fraction(1)
    for j in range(len(matrix)):
        pivot_index = next((i for i in range(j, len(matrix)) if matrix[i][j]), None)
        if pivot_index is None:
            return 0
        if pivot_index != j:
            matrix[j], matrix[pivot_index] = matrix[pivot_index], matrix[j]
            result = -result
        pivot = matrix[j][j]
        result *= pivot
        for i in range(j + 1, len(matrix)):
            multiple = matrix[i][j] / pivot
            if multiple:
                matrix[i] = [a - multiple * b for a, b in zip(matrix[i], matrix[j], strict=True)]
    assert result.denominator == 1
    return result.numerator


def count_possible_sign_extensions(sign_matrix):
    """Replay all candidates surviving the necessary binary intersections."""
    columns = [sum((value == -1) << i for i, value in enumerate(col))
               for col in zip(*sign_matrix, strict=True)]
    # Up to sign, the candidate's first entry is positive. Its weight is
    # 14 and each nonconstant column must have intersection 7 with it.
    equations = [((1 << ORDER) - 2, 0), *((col, 1) for col in columns[1:])]
    pivots = {}
    for equation, rhs in equations:
        while equation:
            pivot = equation.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = (equation, rhs)
                break
            known, parity = pivots[pivot]
            equation ^= known
            rhs ^= parity
        else:
            assert rhs == 0

    rows = sorted(pivots.items())

    def complete(free, affine):
        for pivot, (equation, rhs) in rows:
            bit = (free & equation).bit_count() % 2 ^ (rhs if affine else 0)
            free |= bit << pivot
        return free

    candidates = [complete(0, True)]
    for j in range(1, ORDER):
        if j not in pivots:
            move = complete(1 << j, False)
            candidates += [candidate ^ move for candidate in candidates]
    assert all(all((mask & candidate).bit_count() % 2 == rhs for mask, rhs in equations)
               for candidate in candidates)
    balanced = [candidate for candidate in candidates if candidate.bit_count() == ORDER // 2]
    exact = [candidate for candidate in balanced
             if all((candidate & column).bit_count() == ORDER // 4 for column in columns[1:])]
    return len(candidates), len(balanced), len(exact)


def verify():
    field = range(ORDER - 1)
    squares = {multiply(value, value) for value in field if value}
    assert len(squares) == 13

    def character(value):
        return 0 if value == 0 else (1 if value in squares else -1)

    hadamard = [[1] * ORDER]
    hadamard.extend([1, *(character(subtract(j, i)) - int(i == j) for j in field)] for i in field)
    assert all(dot(a, b) == ORDER * int(i == j)
               for i, a in enumerate(hadamard) for j, b in enumerate(hadamard))

    residual_columns = tuple(j for j in range(ORDER) if prod(hadamard[i][j] for i in TETRAD) == -1)
    assert residual_columns == RESIDUAL_COLUMNS
    kept_columns = tuple(j for j in range(ORDER) if j not in residual_columns)
    transformed = [list(row) for row in hadamard]
    for i in TETRAD:
        transformed[i] = [sum(hadamard[k][j] for k in TETRAD) // 2 - hadamard[i][j]
                          for j in range(ORDER)]
    sign_matrix = [[row[j] * transformed[0][j] for j in kept_columns] for row in transformed]
    residual = [[row[j] for j in residual_columns] for row in transformed]

    assert len(kept_columns) == 16
    assert all(value in (-1, 1) for row in sign_matrix for value in row)
    assert all(value == 1 for value in sign_matrix[0]) and all(row[0] == 1 for row in sign_matrix)
    for i, (row, r) in enumerate(zip(sign_matrix, residual, strict=True)):
        assert dot(r, r) == 12 and sum(r) % 4 == 2
        assert all(value % 2 == int(i not in TETRAD) for value in r)
        assert prod(row) == (1 if i in TETRAD else -1)
    augmented = [a + r for a, r in zip(sign_matrix, residual, strict=True)]
    columns = list(zip(*augmented, strict=True))
    assert all(dot(a, b) == ORDER * int(i == j)
               for i, a in enumerate(augmented) for j, b in enumerate(augmented))
    assert all(dot(a, b) == ORDER * int(i == j)
               for i, a in enumerate(columns) for j, b in enumerate(columns))
    assert all(sum(column) == 0 for column in columns[16:])
    minor = determinant([residual[i] for i in MINOR_ROWS])
    assert minor == -20480 and minor % 7 == 2

    print(f"28x16 exact partial Hadamard, D12+ residual, doubled-frame minor={minor}")
    total, balanced, exact = count_possible_sign_extensions(sign_matrix)
    assert (total, balanced, exact) == (2048, 586, 0)
    print(f"28x16 direct replay: {total} binary candidates, {balanced} balanced, {exact} exact extensions")


if __name__ == "__main__":
    verify()
