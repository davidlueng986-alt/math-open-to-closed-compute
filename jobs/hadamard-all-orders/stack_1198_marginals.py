"""Verify two separate exact marginal stacks and their common matching deficit."""
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198_channels import signatures
from stack_1198_energy import check_boundary
from stack_1198_joint import dot
from stack_1198_reciprocal import reciprocal_channels
from verify import verify_orthogonal


def match(left, right, fixed=(), maximize_zeros=False):
    supply = defaultdict(list)
    for i, key in enumerate(left):
        supply[key].append(i)
    remaining = set(range(len(right))) - set(LOWER_OMITTED)
    pairs = {}
    for j in fixed:
        pairs[supply[right[j]].pop()] = j
        remaining.remove(j)
    if maximize_zeros:
        for j in sorted(remaining):
            stock = supply[right[j]]
            if stock:
                pairs[stock.pop()] = j
                remaining.remove(j)
    left_groups, right_groups = defaultdict(list), defaultdict(list)
    for (first, second), indices in supply.items():
        left_groups[first].extend((second, i) for i in indices)
    for j in remaining:
        first, second = right[j]
        right_groups[first].append((second, j))
    for first, entries in left_groups.items():
        for (_, i), (_, j) in zip(sorted(entries), sorted(right_groups[first]), strict=True):
            pairs[i] = j
    assert set(pairs) == set(range(len(left)))
    assert set(pairs.values()) == set(range(len(right))) - set(LOWER_OMITTED)
    return pairs


def packed_columns(upper, lower, dots_a, dots_b, pairs, first, candidate, fixed=()):
    n, m = len(upper), len(lower)
    lower_mask = (1 << m) - 1
    packed = []
    for i, col in enumerate(upper):
        j = pairs[i]
        a, ax = dots_a[i]
        b, bx = dots_b[j]
        orientation = -1 if (a or ax) * (b or bx) > 0 else 1
        assert a + orientation * b == 0
        if j in fixed:
            assert ax + orientation * bx == 0
        attached = lower[j] if orientation == 1 else lower[j] ^ lower_mask
        packed.append(col | (attached << n))
    packed.append(first)
    assert verify_orthogonal(n + m, packed) == 715806
    residuals = [dot(n + m, col, candidate) for col in packed]
    assert residuals[-1] == 0
    return packed, residuals


def digest(columns):
    return sha256(''.join(f'{col:x}\n' for col in columns).encode('ascii')).hexdigest()


def verify_case(raw, expected):
    upper, base = source_matrices()
    n, m = len(upper), len(base)
    u = flipped_column(n, UPPER_FLIPS)
    v = flipped_column(m, LOWER_FLIPS)
    for index_list, count, bound in (('upper_flips', 34, n), ('dense_holes', 36, m // 2),
                                      ('sparse_support', 36, m // 2)):
        indices = raw[index_list]
        assert len(indices) == len(set(indices)) == count and all(0 <= i < bound for i in indices)
    assert raw['sparse_negative'] in raw['sparse_support']
    x = upper[raw['upper_pivot']] ^ sum(1 << i for i in raw['upper_flips'])
    lower, y = reciprocal_channels(base, v, raw)
    assert verify_orthogonal(m, lower) == 719400
    assert [dot(m, v, col) for col in lower] == [dot(m, v, col) for col in base]
    assert dot(n, u, x) == dot(m, v, y) == 0
    check_boundary(lower, v, y)
    first, second = u | (v << n), x | (y << n)
    a, deck_a = signatures(upper, u, x)
    b, deck_b = signatures(lower, v, y)
    kept = [j for j in range(m) if j not in LOWER_OMITTED]
    sym = [j for j in kept if j < m // 2]
    assert len(sym) == 597
    for axis in (0, 1):
        assert Counter(abs(pair[axis]) for pair in a) == Counter(abs(b[j][axis]) for j in kept)
    packed, residuals = packed_columns(upper, lower, a, b, match(deck_a, deck_b, sym), first, second, sym)
    assert Counter(map(abs, residuals)) == expected['histogram']
    assert sum(d * d for d in residuals) == expected['energy']
    assert digest([*packed, second]) == expected['original_hash']
    reverse_a, reverse_deck_a = signatures(upper, x, u)
    reverse_b, reverse_deck_b = signatures(lower, y, v)
    alternate = match(reverse_deck_a, reverse_deck_b)
    alternate_packed, _ = packed_columns(upper, lower, reverse_a, reverse_b, alternate, second, first)
    assert digest(alternate_packed) == expected['alternate_hash']
    intersection = Counter(deck_a) & Counter(deck_b[j] for j in kept)
    upper_bound = sum(intersection.values()) + 1
    assert upper_bound == expected['max_zeros']
    maximum = match(deck_a, deck_b, sym, maximize_zeros=True)
    _, best_residuals = packed_columns(upper, lower, a, b, maximum, first, second, sym)
    assert best_residuals.count(0) == upper_bound
    return alternate_packed


def projective_phase(raw, phase_data):
    _, source = source_matrices()
    side, prime = len(source) // 2, len(source) // 2 - 1
    mask = (1 << side) - 1
    a, b, c, d = phase_data['matrix']
    phase = phase_data['phase']
    assert phase in (-1, 1)
    residues = {i * i % prime for i in range(1, prime)}
    assert (a * d - b * c) % prime in residues
    images, column_signs, row_signs = [], [], []
    for idx in range(side):
        x, y = (1, idx - 1) if idx else (0, 1)
        u, v = (a * x + b * y) % prime, (c * x + d * y) % prime
        target = 1 + v * pow(u, -1, prime) % prime if u else 0
        scalar = u or v
        assert scalar
        sign = phase if scalar in residues else -phase
        images.append(target)
        column_signs.append(sign)
        row_signs.append(-sign if bool(idx) != bool(target) else sign)
    assert len(set(images)) == side

    def acted(word):
        return sum((((word >> i) & 1) ^ (row_signs[i] < 0)) << j for i, j in enumerate(images))

    # Independently verify the signed spectral permutation on the entire Paley basis.
    for j, col in enumerate(source[side:]):
        expected = source[side + images[j]] & mask
        if column_signs[j] < 0:
            expected ^= mask
        assert acted(col) == expected
    anti_omit, = [j - side for j in LOWER_OMITTED if j >= side]
    assert images[anti_omit] == anti_omit and column_signs[anti_omit] == 1
    pivot = raw['lower_pivot'] - side
    assert column_signs[pivot] == 1 and images[pivot] == 309
    return dict(raw, lower_pivot=side + images[pivot], dense_holes=[images[i] for i in raw['dense_holes']])


def verify():
    path = Path(__file__).with_name('stack_1198_marginals_data.json')
    data = json.loads(path.read_text(encoding='ascii'))
    common = dict(histogram={0: 1008, 4: 174, 8: 8, 12: 6, 16: 1}, energy=4416, max_zeros=1082,
                  original_hash='efe6700ebc4b22703fe71ae8f2edae70cd1dfcff5a972e24ee9aefc8822d71fc',
                  alternate_hash='6adb514d2f223a1b6457481fcb47ff51677564e946781495058dd5a01c336c11')
    original = verify_case(data['base'], common)
    print('same-source marginal stacks: two exact width-1197 matchings; all 597 symmetric slots exact in the original-first matching')
    print('conditional common matching: exactly 1082 maximum zero dots; joint deficit 115')
    print('same-source original-first sorted residual energy 4416; alternate exact packed SHA256', digest(original))
    projected = projective_phase(data['base'], data['projective'])
    projected_expected = dict(histogram={0: 979, 4: 188, 8: 21, 12: 5, 16: 3, 20: 1}, energy=6240, max_zeros=1103,
                              original_hash='00ea4ead8e7a22810028c69d46156af2210c5fa8f697a64811651c4934ec3bf9',
                              alternate_hash='939d528498e906f5a8a18034e5505978cc7eb473afaee0bbd0cbb881410adc1d')
    alternate = verify_case(projected, projected_expected)
    print('projective anti phase: both marginals exact; 597 exact symmetric slots; exactly 1103 maximum zero dots; joint deficit 94')
    print('projective sorted residual energy 6240; alternate exact packed SHA256', digest(alternate))


if __name__ == '__main__':
    verify()
