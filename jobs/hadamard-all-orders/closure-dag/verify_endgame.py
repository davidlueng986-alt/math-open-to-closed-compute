"""Check exact terminal extension and replacement against direct sign enumeration."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product

from verify_pivot import fixed_size_masks, paley, require, verify_orthogonal


def echelon(rows):
    if not rows:
        return [], []
    matrix = [list(map(Fraction, row)) for row in rows]
    pivots = []
    for column in range(len(matrix[0])):
        head = len(pivots)
        pivot = next((i for i in range(head, len(matrix)) if matrix[i][column]), None)
        if pivot is None:
            continue
        pivots.append(column)
        matrix[head], matrix[pivot] = matrix[pivot], matrix[head]
        pivot_value = matrix[head][column]
        matrix[head] = [x / pivot_value for x in matrix[head]]
        for i, row in enumerate(matrix):
            if i != head and (scale := row[column]):
                matrix[i] = [x - scale * y for x, y in zip(row, matrix[head], strict=True)]
    return matrix[:len(pivots)], pivots


def dot(left, right):
    return sum(x * y for x, y in zip(left, right, strict=True))


def kernel_lift(n, columns, defect):
    require(n >= defect and len(columns) == n - defect, "input column count")
    verify_orthogonal(n, columns)
    signed_columns = [[1 if word >> i & 1 else -1 for i in range(n)] for word in columns]
    equations, pivot_positions = echelon(signed_columns)
    coordinate_positions = [i for i in range(n) if i not in pivot_positions]
    require(len(coordinate_positions) == defect, "kernel dimension")

    # Free coordinates of the reduced system supply the identity minor directly.
    unit = [[int(i == j) for j in range(defect)] for i in range(defect)]
    lift = [None] * n
    for i, row in zip(coordinate_positions, unit, strict=True):
        lift[i] = row
    for i, row in zip(pivot_positions, equations, strict=True):
        lift[i] = [-row[j] for j in coordinate_positions]
    kernel_columns = list(zip(*lift, strict=True))
    require(all(dot(column, vector) == 0 for column in signed_columns for vector in kernel_columns),
            "lift columns are in the kernel")
    return signed_columns, coordinate_positions, lift


def oriented_mask(signs):
    return sum(1 << i for i, x in enumerate(signs) if x == signs[0])


def check_projector(n, columns, positions, lift, quadratic_rows, pairs):
    partial_rows = [[column[i] for column in columns] for i in range(n)]
    kernel_gram = [[n * (i == j) - dot(row, other) for j, other in enumerate(partial_rows)]
                   for i, row in enumerate(partial_rows)]
    for i in range(n):
        require(kernel_gram[i][i] == 8, "projector diagonal")
        for j in range(i + 1):
            require(dot(kernel_gram[i], kernel_gram[j]) == n * kernel_gram[i][j],
                    "scaled projector identity")

    projected_rows = [tuple(row[i] for i in positions) for row in kernel_gram]
    gram = [projected_rows[i] for i in positions]
    _, pivots = echelon(gram)
    require(len(pivots) == 8, "pivot Gram invertibility")
    off_diagonal = [gram[i][j] for i, j in pairs]
    require(all(g % 2 == 0 and -6 <= g <= 6 for g in off_diagonal), "off-diagonal pivot Gram alphabet")
    transposed = list(zip(*gram, strict=True))
    for r, ell in zip(projected_rows, lift, strict=True):
        require(all(x % 2 == 0 and -8 <= x <= 8 for x in r), "projected type alphabet")
        require(tuple(dot(ell, column) for column in transposed) == r, "projector lift")
        require(dot(ell, r) == 8, "projected type norm")
    types = Counter(projected_rows)
    for i in range(8):
        for j in range(i + 1):
            require(sum(count * r[i] * r[j] for r, count in types.items()) == n * gram[i][j],
                    "projected type multiplicity sum")
    moments = [1] + [Fraction(gram[i][j], 8) for i, j in pairs]
    require(all(dot(row, moments) == 0 for row in quadratic_rows), "common quadratic null vector")
    return len(types)


def normalized_extensions(n, columns):
    """Return extension masks after quotienting by global change of sign."""
    signed_columns, coordinate_positions, lift = kernel_lift(n, columns, 8)
    pairs = list(combinations(range(8), 2))
    coefficients = [[dot(row, row) - 1] + [2 * row[i] * row[j] for i, j in pairs] for row in lift]
    basis, _ = echelon(coefficients)
    types = check_projector(n, signed_columns, coordinate_positions, lift, coefficients, pairs)
    extensions = set()
    for rest in product((-1, 1), repeat=7):
        sigma = (1,) + rest
        character_values = [1] + [sigma[i] * sigma[j] for i, j in pairs]
        lifted = [dot(row, sigma) for row in lift]
        integral = all(abs(x) == 1 for x in lifted)
        reduced = all(dot(row, character_values) == 0 for row in basis)
        require(integral == reduced, "quadratic row-span test")
        if integral:
            # Use a positive first original row for the comparison with direct enumeration.
            extensions.add(oriented_mask(lifted))
    require(len(basis) <= (21 if extensions else 28), "coefficient rank bound")
    return extensions, len(basis), types


def direct_extensions(n, columns):
    require(columns[0] == (1 << n) - 1, "balance equation for direct enumeration")
    balanced = (1 | (mask << 1) for mask in fixed_size_masks(n - 1, n // 2 - 1))
    return {
        candidate for candidate in balanced
        if all((column ^ candidate).bit_count() == n // 2 for column in columns[1:])
    }


def check(n, columns):
    extensions, rank, types = normalized_extensions(n, columns)
    require(extensions == direct_extensions(n, columns), "complete comparison against ordinary sign enumeration")
    print(f"n={n}: all 128 kernel patterns agree with direct enumeration; "
          f"{len(extensions)} extensions up to sign, coefficient rank {rank}, {types} projected types")
    return len(extensions)


def check_replacement(columns):
    n = 12
    retained = columns[:-1]
    _, _, lift = kernel_lift(n, retained, 9)
    candidates = set()
    for rest in product((-1, 1), repeat=8):
        sigma = (1,) + rest
        lifted = [dot(row, sigma) for row in lift]
        if all(abs(x) == 1 for x in lifted):
            candidates.add(oriented_mask(lifted))
    require(candidates == direct_extensions(n, retained), "complete nine-dimensional enumeration")
    pairs = [(left, right) for left, right in combinations(sorted(candidates), 2)
             if (left ^ right).bit_count() == n // 2]
    require(len(candidates) == 82 and len(pairs) == 1296, "order-12 replacement counts")
    require(all(columns[-1] not in pair for pair in pairs), "each pair replaces the last old column")
    verify_orthogonal(n, [*retained, *pairs[0]])
    print(f"n={n}, last column deleted: all 256 patterns agree with direct enumeration; "
          f"{len(candidates)} candidates up to sign and {len(pairs)} orthogonal pairs")


if __name__ == "__main__":
    require(check(20, paley(19)[:12]) > 0, "Paley extension control")
    # H(4) with each row repeated three times. A fifth orthogonal sign column
    # would require four zero sums over triples of signs.
    repeated = [sum(7 << (3 * i) for i in range(4) if word >> i & 1) for word in paley(3)]
    require(check(12, repeated) == 0, "odd repeated-row control")
    check_replacement(repeated)
