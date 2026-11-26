"""Verify a D20+ code whose characteristic frame has the wrong phase."""

from itertools import combinations

from r_paley_isotropic_code import assemble, dot, half_projections, maximal_set
from r_paley_order44_classifier import code_signs, lattice_roots, reduced_rows
from verify import paley, verify_orthogonal


CHOSEN = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 14)
BLOCKS = (
    ((0, 1, 3, 4), ((3, -1, -1, 0), (1, 3, 0, -1), (1, 0, 3, 1), (0, 1, -1, 3))),
    ((2, 5, 6, 7), ((1, -1, 3, 0), (1, 1, 0, -3), (3, 0, -1, 1), (0, 3, 1, 1))),
)


def reserve_columns():
    columns = []
    for positions, block in BLOCKS:
        for column in block:
            padded = [0]*8
            for i, value in zip(positions, column, strict=True):
                padded[i] = value
            columns.append(padded)
    assert all(dot(a, a) == 11 for a in columns)
    assert all(not dot(a, b) for a, b in combinations(columns, 2))
    assert len(reduced_rows(columns, 11)[1]) == 4
    return columns


def verify():
    source = paley(19)
    assert verify_orthogonal(20, source) == 190
    unused = [j for j in range(20) if j not in CHOSEN]
    reserve = reserve_columns()
    x = [[2*(source[j] >> i & 1)-1 for j in CHOSEN] for i in range(20)]
    v = [[2*(source[j] >> i & 1)-1 for j in unused] for i in range(20)]
    matrix = [a+[dot(b, c) for c in reserve] for a, b in zip(x, v, strict=True)]
    row_residues = {sum(row) % 4 for row in matrix}
    assert len(row_residues) == 1
    parity = ((row_residues.pop()-2)//2) % 2

    masks = list(code_signs(matrix))
    assert len(masks) == len(set(masks)) == 20
    assert all(mask.bit_count() % 2 != parity for mask in masks)
    assert verify_orthogonal(20, masks) == 190
    factor = []
    for mask in masks:
        word = [1-2*(mask >> i & 1) for i in range(20)]
        numerator = [dot(row, word) for row in matrix]
        assert all(value in (-20, 0, 20) for value in numerator)
        column = tuple(value//20 for value in numerator)
        assert dot(column, column) == 5
        factor.append(column)
    factor_rows = tuple(zip(*factor, strict=True))
    for i, j in combinations(range(20), 2):
        assert 2*dot(factor_rows[i], factor_rows[j]) == dot(v[i], v[j])
    assert all(dot(row, row) == 5 for row in factor_rows)
    assert lattice_roots(matrix) == (0, 760)

    lower = [z for z in range(1, 1 << 20, 2)
             if all(abs(10-(z ^ source[j]).bit_count()) == 1 for j in CHOSEN)]
    vectors = [tuple(half_projections(source, z)[j] for j in unused) for z in lower]
    frame = maximal_set(11, vectors, 20)
    assert len(lower) == 312 and len(frame) == 12
    physical = assemble(11, source, CHOSEN, [lower[j] for j in frame])
    assert len(physical) == 36 and verify_orthogonal(44, physical) == 630
    print('Order 44: D20+ code with all 20 characteristic lines in the wrong phase; fixed exterior width 36')


if __name__ == '__main__':
    verify()
