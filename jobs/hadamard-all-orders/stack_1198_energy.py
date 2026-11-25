"""Verify the folded Paley residue gap and the energy-4032 next column."""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198_auxiliary import FIRST, frames, multiply
from stack_1198_joint import dot, lower_channels, signature
from verify import paley, rows_from_columns, verify_orthogonal


def check_row_pattern_bound():
    size = 600
    rows = rows_from_columns(size, paley(size - 1))
    bound = max(abs(size - 2 * (rows[0] ^ rows[1] ^ rows[2] ^ row).bit_count()) for row in rows[3:])
    assert bound == 48
    four, five = (size + bound) // 8, (size + 5 * bound) // 16
    assert (four, five) == (81, 52) and max(four, 2 * five) < 150
    print('folded Paley energy gap: quartic bound 48; row pattern caps 81 and 52')


def check_fold(lower, original):
    side = len(lower) // 2
    mask = (1 << side) - 1
    symmetric, alternating = lower[:side], lower[side:]
    assert all(col >> side == col & mask for col in symmetric)
    assert all(col >> side == (col & mask) ^ mask for col in alternating)
    assert symmetric == original[:side]
    p = rows_from_columns(side, [col & mask for col in symmetric])
    q = rows_from_columns(side, [col & mask for col in alternating])
    assert sorted(min(row, row ^ mask) for row in p) == sorted(min(row, row ^ mask) for row in q)


def check_boundary(lower, v, y):
    m = len(lower)
    first = [dot(m, v, lower[j]) for j in LOWER_OMITTED]
    beta = tuple(dot(m, y, lower[j]) * (1 if value > 0 else -1)
                 for j, value in zip(LOWER_OMITTED, first, strict=True))
    assert tuple(map(abs, first)) == tuple(2 * value for value in FIRST)
    r = tuple(tuple(1 - 2 * (i == j) for j in range(4)) for i in range(4))
    for e, _, _ in frames()[0]:
        k = tuple(tuple(value // 2 for value in row) for row in multiply(e, r))
        assert tuple(sum(a*b for a,b in zip(row, r[0], strict=True)) for row in k) == tuple(map(abs, first))
        for f in product((1, -1), repeat=4):
            if sum(a*b for a,b in zip(f, r[0], strict=True)) == 0:
                if tuple(sum(a*b for a,b in zip(row, f, strict=True)) for row in k) == beta:
                    return
    raise ValueError('omitted projection is outside the compatible frames')


def grouped(size, columns, first, second, omitted=()):
    result = defaultdict(list)
    for j, col in enumerate(columns):
        if j not in omitted:
            a, b = dot(size, first, col), dot(size, second, col)
            key, val = signature(a, b)
            result[key].append((val, j, a, b))
    return result


def check_linear_threshold(lower):
    m = len(lower)
    half = m // 2
    w = {2: 2, 5: -2, half + 2: 2, half + 5: -2}
    coeffs = [sum(wi * (2 * (col >> i & 1) - 1) for i, wi in w.items()) for col in lower]
    assert set(coeffs) == {0, -8, 8} and sum(value != 0 for value in coeffs) == 300
    assert all(coeffs[j] == 0 for j in LOWER_OMITTED)
    # s=M^T w/8, hence M s =150 w and 4s attains squared energy 4800.
    assert sum((value // 2)**2 for value in coeffs) == 4800


def verify():
    path = Path(__file__).with_name('stack_1198_transport_data.json')
    witness = json.loads(path.read_text(encoding='ascii'))['distinct_cap8']['words']
    upper, original = source_matrices()
    n, m = len(upper), len(original)
    u, v = flipped_column(n, UPPER_FLIPS), flipped_column(m, LOWER_FLIPS)
    x = upper[witness['upper_pivot']] ^ sum(1 << i for i in witness['upper_flips'])
    lower, y = lower_channels(original, v, witness)
    check_fold(lower, original)
    check_linear_threshold(lower)
    assert dot(n, u, x) == dot(m, v, y) == 0
    check_boundary(lower, v, y)
    top = grouped(n, upper, u, x)
    bottom = grouped(m, lower, v, y, LOWER_OMITTED)
    assert top.keys() == bottom.keys()
    signed = [None] * n
    expected = 0
    for group in top:
        for (a, i, first_a, second_a), (b, j, first_b, second_b) in zip(
            sorted(top[group]), sorted(bottom[group]), strict=True
        ):
            sign = -1 if (first_a or second_a) * (first_b or second_b) > 0 else 1
            signed[i] = lower[j] if sign == 1 else lower[j] ^ ((1 << m) - 1)
            assert first_a + sign * first_b == 0 and abs(second_a + sign * second_b) == abs(a - b)
            expected += (a - b)**2
    columns = [a | (b << n) for a, b in zip(upper, signed, strict=True)] + [u | (v << n)]
    assert verify_orthogonal(n + m, columns) == 715806
    new = x | (y << n)
    residues = [dot(n + m, c, new) for c in columns]
    assert residues[-1] == 0 and Counter(map(abs, residues)) == {0: 972, 4: 216, 8: 9}
    assert sum(d*d for d in residues) == expected == 4032
    transform = [sum(d // 4 * (2 * (col >> row & 1) - 1)
                     for d, col in zip(residues[:-1], signed, strict=True) if d) for row in range(m)]
    assert sum(value*value for value in transform) == m * (4032 // 16)
    assert any(value % 75 for value in transform)
    digest = sha256(''.join(f'{col:x}\n' for col in [*columns, new]).encode('ascii')).hexdigest()
    print('stacked next column: 972 zero, 216 magnitude 4, 9 magnitude 8; squared energy 4032')
    print('stacked energy-4032 packed SHA256', digest)


if __name__ == '__main__':
    check_row_pattern_bound()
    verify()
