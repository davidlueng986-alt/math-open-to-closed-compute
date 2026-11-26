"""Verify stacked sign witnesses in the dense 34, sparse 30 boundary direction."""
from collections import Counter
import json
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198_channels import signatures
from stack_1198_energy import check_boundary
from stack_1198_joint import dot
from stack_1198_marginals import digest, match, packed_columns
from stack_1198_reciprocal import reciprocal_channels
from verify import verify_orthogonal


def row_mask(indices):
    return sum(1 << index for index in indices)


def reconstruct(witness):
    upper, base = source_matrices()
    n, m = len(upper), len(base)
    side = m // 2
    mask = (1 << side) - 1
    u, v = flipped_column(n, UPPER_FLIPS), flipped_column(m, LOWER_FLIPS)
    p = witness['upper_pivot']
    q = witness['lower_pivot']
    omit = witness['sparse_omit']
    phase = witness['dense_phase']
    sign = witness['sparse_sign']
    anti_omit, = (j for j in LOWER_OMITTED if j >= side)
    assert 0 < p < n and side <= q < m and q not in LOWER_OMITTED
    assert omit in LOWER_OMITTED and omit < side
    assert phase in (-1, 1) and sign in (-1, 1)

    for key, count, limit in (('upper_flips', 32, n), ('dense_holes', 30, side),
                              ('dense_reverse', 2, side), ('sparse_support', 30, side)):
        entries = witness[key]
        assert len(entries) == len(set(entries)) == count
        assert all(0 <= i < limit for i in entries)
    assert set(witness['dense_holes']).isdisjoint(witness['dense_reverse'])
    saturation = ((base[q] ^ base[anti_omit]) & mask)
    changed = [*witness['dense_holes'], *witness['dense_reverse']]
    assert len({saturation >> i & 1 for i in changed}) == 1

    x = upper[p] ^ row_mask(witness['upper_flips'])
    dense_input = list(base)
    dense_input[q] ^= row_mask(witness['dense_reverse'])
    if phase < 0:
        dense_input[q] ^= mask
    lower, y = reciprocal_channels(dense_input, v, witness)
    lower[q] = base[q]
    assert lower[side:] == base[side:]
    assert verify_orthogonal(m, lower) == 719400
    assert [dot(m, v, col) for col in lower] == [dot(m, v, col) for col in base]
    assert dot(n, u, x) == dot(m, v, y) == 0
    check_boundary(lower, v, y)
    boundary = tuple(dot(m, y, lower[j]) // 2 * (1 if dot(m, v, lower[j]) > 0 else -1)
                     for j in LOWER_OMITTED)
    assert abs(boundary[2]) == 34 and abs(boundary[3]) == 30
    assert abs(dot(n, x, upper[p])) == abs(dot(m, y, lower[q])) == 1132
    return upper, lower, u, v, x, y, boundary


def verify_case(witness):
    upper, lower, u, v, x, y, boundary = reconstruct(witness)
    n, m = len(upper), len(lower)
    first, second = u | (v << n), x | (y << n)
    a, deck_a = signatures(upper, u, x)
    b, deck_b = signatures(lower, v, y)
    kept = tuple(j for j in range(m) if j not in LOWER_OMITTED)
    symmetric = tuple(j for j in kept if j < m // 2)
    assert len(symmetric) == 597
    assert Counter(abs(row[0]) for row in a) == Counter(abs(b[j][0]) for j in kept)
    second_deck = Counter(abs(row[1]) for row in a)
    second_lower = Counter(abs(b[j][1]) for j in kept)
    second_missing = sum((second_deck - second_lower).values())
    packed, residuals = packed_columns(upper, lower, a, b, match(deck_a, deck_b, symmetric),
                                        first, second, symmetric)
    _, best_residuals = packed_columns(upper, lower, a, b,
                                        match(deck_a, deck_b, symmetric, maximize_zeros=True),
                                        first, second, symmetric)
    max_zeros = sum((Counter(deck_a) & Counter(deck_b[j] for j in kept)).values()) + 1
    assert best_residuals.count(0) == max_zeros
    assert second_missing == 0
    ra, deck_ra = signatures(upper, x, u)
    rb, deck_rb = signatures(lower, y, v)
    alternate, _ = packed_columns(upper, lower, ra, rb, match(deck_ra, deck_rb), second, first)
    return {'boundary': list(boundary),
            'histogram': dict(sorted(Counter(map(abs, residuals)).items())),
            'energy': sum(r * r for r in residuals), 'max_zeros': max_zeros,
            'sorted_hash': digest([*packed, second]), 'alternate_hash': digest(alternate)}


def main():
    path = Path(__file__).with_name('stack_1198_dense_boundary_data.json')
    record = json.loads(path.read_text(encoding='ascii'))
    observed = verify_case(record['witness'])
    expected = record['expected']
    expected['histogram'] = {int(k): v for k, v in expected['histogram'].items()}
    assert observed == expected, observed
    print('dense boundary: two exact width-1197 marginal stacks; 597 exact symmetric slots')
    print('dense boundary:', observed)


if __name__ == '__main__':
    main()
