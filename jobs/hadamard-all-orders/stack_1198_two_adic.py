"""Compute the modulo-sixteen liftable parity subspace of the two fixed stacks."""

from collections import Counter
from itertools import product

from stack_1197 import (LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, assemble, flipped_column,
                         source_matrices)
from stack_1197_four_channels import LOWER_OMITTED as FOUR_OMITTED, sources as four_sources
from stack_1198_auxiliary import frames, multiply
from verify import rows_from_columns


def triangular(weights, width, bits):
    """Eliminate modulo 2^bits and record the successive triangular congruences."""
    stride = 2 * bits + 1
    ones = ((1 << (stride * width)) - 1) // ((1 << stride) - 1)
    # The guard prevents borrowing between packed entries in a row subtraction.
    guard = ones << (2 * bits)
    full_modulus = 1 << bits
    rows = [sum((x & (full_modulus - 1)) << (stride * j) for j, x in enumerate(row))
            for row in weights]
    active = ones
    result = []
    for exponent in range(bits, 0, -1):
        modulus = 1 << exponent
        while rows:
            row_index = next((i for i, row in enumerate(rows) if row & active), None)
            if row_index is None:
                break
            pivot = rows.pop(row_index)
            odd = pivot & active
            bit = odd & -odd
            low = bit.bit_length() - 1
            inverse = pow((pivot >> low) & (modulus - 1), -1, modulus)
            pivot = (inverse * pivot) & (active * (modulus - 1))
            result.append((exponent, low // stride, pivot))
            active ^= bit
            mask = active * (modulus - 1)
            tail = pivot & mask
            rows = [(row + guard - ((row >> low) & (modulus - 1)) * tail) & mask for row in rows]
        mask = active * (modulus - 1)
        rows = [(row & mask) >> 1 for row in rows]
    return result, stride


def projection_code(pivots, stride, width):
    """Give each coordinate as a packed linear form in the free binary coordinates."""
    pivot_indices = {j for _, j, _ in pivots}
    free_indices = [i for i in range(width) if i not in pivot_indices]
    coordinate = {i: 1 << j for j, i in enumerate(free_indices)}
    ones = ((1 << (stride * width)) - 1) // ((1 << stride) - 1)
    for _, index, packed in reversed(pivots):
        support = (packed & ones) ^ (1 << (stride * index))
        value = 0
        while support:
            bit = support & -support
            value ^= coordinate[(bit.bit_length() - 1) // stride]
            support ^= bit
        coordinate[index] = value
    return [coordinate[i] for i in range(width)]


def check_control(entries):
    rows, stride = triangular(entries, 3, 4)
    forms = projection_code(rows, stride, 3)
    expected = set()
    for point in product(range(16), repeat=3):
        legal = all(sum(a*b for a, b in zip(row, point, strict=True)) % 16 == 0 for row in entries)
        diagonal = all(sum((row >> (stride*i) & 15)*value for i, value in enumerate(point)) % (1 << e) == 0
                       for e, _, row in rows)
        assert legal == diagonal
        if legal:
            expected.add(tuple(value & 1 for value in point))
    observed = {tuple((word & form).bit_count() & 1 for form in forms)
                for word in range(1 << (3 - len(rows)))}
    assert expected == observed


def stack_frames(upper, lower, u, v, omitted):
    n, m = len(upper), len(lower)
    stack = assemble(upper, lower, u, v, omitted)
    rows_a = rows_from_columns(n, upper)
    rows_b = rows_from_columns(m, [word >> n for word in stack[:-1]])
    u_signs = [2 * (u >> i & 1) - 1 for i in range(n)]
    cross = [[sign * (2 * (row ^ col).bit_count() - n)
              for sign, col in zip(u_signs, rows_a, strict=True)] for row in rows_b]
    universe = (1 << m) - 1
    boundary = [lower[j] ^ (universe if m - 2 * (v ^ lower[j]).bit_count() < 0 else 0) for j in omitted]
    r = tuple(tuple(1 - 2 * (i == j) for j in range(4)) for i in range(4))
    for e, _, _ in frames()[0]:
        k = tuple(tuple(x // 2 for x in row) for row in multiply(e, r))
        dk = [tuple(r[0][j] * sum((2 * (col >> i & 1) - 1) * k[l][j] for l, col in enumerate(boundary))
                    for j in range(4)) for i in range(m)]
        rows = [a + list(b) for a, b in zip(cross, dk, strict=True)]
        assert all(sum(row) == m * (2 * (v >> i & 1) - 1) for i, row in enumerate(rows))
        yield rows, k, r[0]


def boundary_patterns(linear_forms, dimension):
    span = {0}
    for i in range(dimension):
        residue = sum(((form >> i) & 1) << j for j, form in enumerate(linear_forms))
        span |= {value ^ residue for value in span}
    return span


def check_stack(label, sources, expected_boundary_counts):
    allowed = set()
    all_projections = set()
    remaining_counts = []
    for weights, k, initial in stack_frames(*sources):
        pivots, stride = triangular(weights, 1200, 4)
        count = Counter(exponent for exponent, _, _ in pivots)
        forms = projection_code(pivots, stride, 1200)
        dimension = 1200 - len(pivots)
        assert dimension == 301 and len(set(forms)) == 1200
        assert count in (Counter({1: 598, 2: 300, 3: 1}), Counter({1: 598, 2: 299, 3: 2}))
        beta = boundary_patterns(forms[-4:], dimension)
        assert beta == (set(range(16)) if count[3] == 1 else {i for i in range(16) if i.bit_count() % 2 == 0})
        remaining_counts.append(len(beta))
        for pattern in range(16):
            signs = tuple(a * (-1 if pattern >> i & 1 else 1) for i, a in enumerate(initial))
            projection = tuple(sum(a*b for a, b in zip(row, signs, strict=True)) // 2 for row in k)
            all_projections.add(projection)
            if pattern in beta:
                allowed.add(projection)
    assert tuple(remaining_counts) == expected_boundary_counts
    assert len(all_projections) == 46
    assert len(allowed) == 30 and sum(v[0] % 2 for v in allowed) == 16
    print(f'{label}: 301 liftable parity dimensions; boundary mask counts {tuple(remaining_counts)}; 30 of 46 oriented projections survive')


def main():
    check_control([(2, 4, 5), (6, 1, 3), (8, 12, 2)])
    check_control([(2, 4, 0), (8, 0, 8), (4, 8, 0)])
    check_stack('four-channel stack', (*four_sources(), FOUR_OMITTED), (16, 8, 16, 8))
    upper, lower = source_matrices()
    u = flipped_column(len(upper), UPPER_FLIPS)
    v = flipped_column(len(lower), LOWER_FLIPS)
    check_stack('two-channel stack', (upper, lower, u, v, LOWER_OMITTED), (8, 16, 8, 16))


if __name__ == '__main__':
    main()
