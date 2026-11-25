"""Exclude tensor-product auxiliary matrices for explicit exact 2396 stacks."""

from collections import Counter
import json
from pathlib import Path

from stack_1197 import (LOWER_FLIPS, LOWER_OMITTED as TWO_OMITTED, UPPER_FLIPS, assemble,
                         flipped_column, source_matrices)
from stack_1197_four_channels import LOWER_OMITTED, sources
from stack_1198_channels import signatures
from stack_1198_four_channels import SHARP_CAP_LOWER, SHARP_CAP_UPPER, sorted_pairing
from stack_1198_marginals import match, packed_columns, projective_phase
from stack_1198_reciprocal import reciprocal_channels
from stack_odd_t_residual import sylvester_four
from verify import paley, rows_from_columns


def ternary_add(left, right):
    """A pair of disjoint bit masks gives the positions of the residues 1 and -1."""
    a, b = left
    c, d = right
    return ((a & ~(c | d)) | (c & ~(a | b)) | (b & d),
            (b & ~(c | d)) | (d & ~(a | b)) | (a & c))


def component_sizes(generators, width):
    rows = list(generators)
    pivot_columns = []
    for column in range(width):
        row_index = len(pivot_columns)
        bit = 1 << column
        other = next((j for j in range(row_index, len(rows)) if (rows[j][0] | rows[j][1]) & bit), None)
        if other is None:
            continue
        pivot_columns.append(column)
        rows[row_index], rows[other] = rows[other], rows[row_index]
        if rows[row_index][1] & bit:
            rows[row_index] = rows[row_index][::-1]
        pivot_row = rows[row_index]
        for j, (positive, negative) in enumerate(rows):
            if j == row_index:
                continue
            if positive & bit:
                rows[j] = ternary_add(rows[j], pivot_row[::-1])
            elif negative & bit:
                rows[j] = ternary_add(rows[j], pivot_row)
        if len(pivot_columns) == len(rows):
            break
    rank = len(pivot_columns)
    assert all(row == (0, 0) for row in rows[rank:])

    parent = list(range(width))

    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for pivot, (positive, negative) in zip(pivot_columns, rows[:rank], strict=True):
        assert (positive | negative) & (1 << pivot)
        rest = (positive | negative) ^ (1 << pivot)
        while rest:
            next_bit = rest & -rest
            parent[root(next_bit.bit_length() - 1)] = root(pivot)
            rest ^= next_bit
    return rank, sorted(Counter(root(i) for i in range(width)).values())


def control():
    original = sylvester_four(paley(11))
    m = len(original)
    packed = rows_from_columns(m, original)
    keep = ((1 << m) - 1) ^ sum(1 << (12*i) for i in range(4))
    # Puncture one fixed position per component, and pack the other 44 positions.
    retained = [i for i in range(m) if keep >> i & 1]
    rows = [sum(1 << i for i, j in enumerate(retained) if row >> j & 1) for row in packed]
    width = len(retained)
    universe = (1 << width) - 1
    assert component_sizes([(row, row ^ universe) for row in rows], width) == (24, [11, 11, 11, 11])


def cross_gram_generators(upper, paired_lower, m):
    """Pack the columns of A B^T over F3 as ternary generators."""
    n = len(upper)
    rows_a = rows_from_columns(n, upper)
    rows_b = rows_from_columns(m, paired_lower)
    generators = []
    for row in rows_b:
        positive, negative = 0, 0
        for i, other in enumerate(rows_a):
            residue = (n - 2 * (other ^ row).bit_count()) % 3
            if residue == 1:
                positive |= 1 << i
            elif residue == 2:
                negative |= 1 << i
        generators.append((positive, negative))
    return generators


def four_channel_pairings():
    upper, lower, u, v = sources()
    n, m = len(upper), len(lower)
    columns = assemble(upper, lower, u, v, LOWER_OMITTED)
    initial = [column >> n for column in columns[:-1]]

    x = upper[411] ^ sum(1 << i for i in SHARP_CAP_UPPER)
    y = lower[30] ^ sum(1 << i for i in SHARP_CAP_LOWER)
    a, deck_a = signatures(upper, u, x)
    b, deck_b = signatures(lower, v, y)
    paired = [None] * n
    for i, j in sorted_pairing(deck_a, deck_b).items():
        a1, a2 = a[i]
        b1, b2 = b[j]
        sign = -1 if (a1 or a2) * (b1 or b2) > 0 else 1
        assert a1 + sign * b1 == 0
        paired[i] = lower[j] if sign > 0 else lower[j] ^ ((1 << m) - 1)
    return upper, m, [('four-channel first stack', initial), ('four-channel E1920 pairing', paired)]


def two_channel_pairings():
    path = Path(__file__).with_name('stack_1198_marginals_data.json')
    data = json.loads(path.read_text(encoding='ascii'))
    upper, original = source_matrices()
    n, m = len(upper), len(original)
    u = flipped_column(n, UPPER_FLIPS)
    v = flipped_column(m, LOWER_FLIPS)
    symmetric = [j for j in range(m // 2) if j not in TWO_OMITTED]
    results = []
    for label, raw in (('two-channel', data['base']),
                       ('projective', projective_phase(data['base'], data['projective']))):
        x = upper[raw['upper_pivot']] ^ sum(1 << i for i in raw['upper_flips'])
        lower, y = reciprocal_channels(original, v, raw)
        for name, first_a, first_b, second_a, second_b, fixed in (
            ('first marginal', u, v, x, y, symmetric),
            ('second marginal', x, y, u, v, ()),
        ):
            a, deck_a = signatures(upper, first_a, second_a)
            b, deck_b = signatures(lower, first_b, second_b)
            pairing = match(deck_a, deck_b, fixed)
            packed, _ = packed_columns(upper, lower, a, b, pairing,
                                       first_a | first_b << n, second_a | second_b << n, fixed)
            results.append((f'{label} {name}', [word >> n for word in packed[:-1]]))
    return upper, m, results


def main():
    control()
    for upper, m, pairings in (four_channel_pairings(), two_channel_pairings()):
        n = len(upper)
        for name, paired in pairings:
            assert len(paired) == n
            assert component_sizes(cross_gram_generators(upper, paired, m), n) == (600, [1196])
            print(f'{name}: punctured ternary code rank 600, one component of size 1196')


if __name__ == '__main__':
    main()
