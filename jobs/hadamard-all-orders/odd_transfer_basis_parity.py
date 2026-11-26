"""Replay the odd Hadamard transfer parity conditions and equality pattern."""

from functools import reduce
from itertools import combinations
from operator import or_, xor

from semiprime_williamson import williamson_blocks
from verify import goethals_seidel, paley, rows_from_columns, verify_orthogonal


def binary_rank(words):
    pivots = {}
    for word in words:
        while word:
            pivot = word.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = word
                break
            word ^= pivots[pivot]
    return len(pivots)


def check_parity_code(parities, rank):
    assert binary_rank(parities) == rank
    assert all(value.bit_count() % 4 == 0 for value in parities)
    assert all((left & right).bit_count() % 2 == 0 for left, right in combinations(parities, 2))


def verify_control():
    width, blocks = 28, 11
    order = width*blocks
    columns = paley(order - 1)
    assert len(columns) == order
    assert verify_orthogonal(order, columns) == 47_278
    rows = rows_from_columns(order, columns)

    basis_columns = goethals_seidel(williamson_blocks(13)[0])
    assert len(basis_columns) == width
    assert verify_orthogonal(width, basis_columns) == 378
    basis = rows_from_columns(width, basis_columns)
    basis_parity = basis[0].bit_count() % 2
    basis = [row ^ basis_parity for row in basis]
    assert all(row.bit_count() % 2 == 0 for row in basis)

    all_rows = (1 << order) - 1
    block_mask = (1 << width) - 1
    parities = []
    for block in range(blocks):
        start = block*width
        mismatch = reduce(xor, (all_rows ^ col for col in columns[start:start+width]), 0)
        assert 4 <= mismatch.bit_count() <= order - 4
        parities.append(mismatch)
        for index, output_row in enumerate(rows):
            restriction = (output_row >> start) & block_mask
            expected = 2*((mismatch >> index) & 1)
            assert all((width - 2*(restriction ^ base_row).bit_count()) % 4 == expected
                       for base_row in basis)

    check_parity_code(parities, 10)
    assert reduce(xor, parities, 0) == 0
    support = reduce(or_, parities, 0).bit_count()
    assert support >= 22
    parities[0] ^= all_rows
    check_parity_code(parities, 11)
    assert reduce(xor, parities, 0) == reduce(or_, parities, 0) == all_rows
    print(f"H(308) / eleven H(28) bases: rank 10 and mismatch support {support}; "
          "opposite reference product covers all 308 rows")


def verify_equality_pattern():
    edges = tuple(3 << (2*index) for index in range(11))
    parities = [edges[index - 1] | edges[index] for index in range(11)]
    check_parity_code(parities, 10)
    assert reduce(xor, parities, 0) == 0
    assert all(word.bit_count() == 4 for word in parities)
    assert reduce(or_, parities, 0).bit_count() == 22
    print("Abstract equality pattern: eleven doubled cycle edges, support 22")


if __name__ == "__main__":
    verify_control()
    verify_equality_pattern()
