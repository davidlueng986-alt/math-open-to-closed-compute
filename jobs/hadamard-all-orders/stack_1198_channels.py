"""Verify an exact anti-channel and the remaining energy-2112 residual."""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198_energy import check_boundary, check_fold, check_row_pattern_bound
from stack_1198_joint import dot, lower_channels, signature
from verify import paley, verify_orthogonal


def check_qr_arithmetic():
    q = 599
    assert pow(2, (q-1)//2, q) == 1 and 24**2 < q <= 25**2
    assert [600 * length // 50**2 for length in (50, 100)] == [12, 24]
    assert (600 + 48) // 8 < 100
    # The analogous binary parity kernel at Paley order eight has minimum weight four.
    columns = paley(7)
    mask = (1 << 8)-1
    code = [packed for bits in product((0, 1), repeat=8)
            if (packed := sum(bit << i for i, bit in enumerate(bits))).bit_count() % 2 == 0
            and all((packed & (col ^ mask)).bit_count() % 2 == 0 for col in columns)]
    assert len(code) == 16 and min(codeword.bit_count() for codeword in code if codeword) == 4


def signatures(columns, first, second):
    size = len(columns)
    dots = [(dot(size, first, col), dot(size, second, col)) for col in columns]
    return dots, [signature(a, b) for a, b in dots]


def match_anti_first(upper_deck, lower_deck):
    n, m = len(upper_deck), len(lower_deck)
    side = m // 2
    supply = defaultdict(list)
    for i, key in enumerate(upper_deck):
        supply[key].append(i)
    remaining = set(range(m)) - set(LOWER_OMITTED)
    anti = sorted(j for j in remaining if j >= side)
    assert len(anti) == 599
    pairs = {}
    for j in anti:
        i = supply[lower_deck[j]].pop()
        pairs[i] = j
        remaining.remove(j)
    left, right = defaultdict(list), defaultdict(list)
    for (first, second), indices in supply.items():
        for i in indices:
            left[first].append((second, i))
    for j in remaining:
        first, second = lower_deck[j]
        right[first].append((second, j))
    assert left.keys() == right.keys()
    for first in left:
        for (_, i), (_, j) in zip(sorted(left[first]), sorted(right[first]), strict=True):
            pairs[i] = j
    assert len(pairs) == n and set(pairs.values()) == set(range(m)) - set(LOWER_OMITTED)
    return pairs


def verify():
    path = Path(__file__).with_name('stack_1198_channels_data.json')
    witness = json.loads(path.read_text(encoding='ascii'))
    upper, original = source_matrices()
    n, m = len(upper), len(original)
    side = m//2
    u, v = flipped_column(n, UPPER_FLIPS), flipped_column(m, LOWER_FLIPS)
    x = upper[witness['upper_pivot']] ^ sum(1 << i for i in witness['upper_flips'])
    lower, y = lower_channels(original, v, witness)
    check_fold(lower, original)
    check_boundary(lower, v, y)
    assert dot(n, u, x) == dot(m, v, y) == 0
    upper_dots, upper_deck = signatures(upper, u, x)
    lower_dots, lower_deck = signatures(lower, v, y)
    pairs = match_anti_first(upper_deck, lower_deck)
    packed, residual_by_lower = [], [0] * m
    for i, a_col in enumerate(upper):
        j = pairs[i]
        a1, a2 = upper_dots[i]
        b1, b2 = lower_dots[j]
        orientation = -1 if (a1 or a2) * (b1 or b2) > 0 else 1
        assert a1 + orientation*b1 == 0
        d = a2 + orientation*b2
        assert d % 4 == 0
        residual_by_lower[j] = orientation*d // 4
        b_col = lower[j] if orientation == 1 else lower[j] ^ ((1 << m)-1)
        packed.append(a_col | (b_col << n))
    packed.append(u | (v << n))
    assert verify_orthogonal(n+m, packed) == 715806
    new = x | (y << n)
    residuals = [dot(n+m, col, new) for col in packed]
    assert Counter(map(abs, residuals)) == {0: 1080, 4: 112, 8: 5}
    assert sum(d*d for d in residuals) == 2112
    assert not any(residual_by_lower[side:])
    transformed = [sum(value*(2*(col >> row & 1)-1)
                       for value, col in zip(residual_by_lower[:side], lower[:side], strict=True) if value)
                   for row in range(side)]
    assert sum(v*v for v in transformed) == side * (2112//16)
    assert any(value % 25 for value in transformed)
    digest = sha256(''.join(f'{col:x}\n' for col in [*packed, new]).encode('ascii')).hexdigest()
    assert digest == 'a21ad0c7df6368773e5b4c61fedace0f0f1474a5e44f83e40f77848b57851c18'
    print('stacked channels: 599 exact anti slots; 1080 zero, 112 magnitude 4, 5 magnitude 8; symmetric energy 2112')
    print('stacked exact anti packed SHA256', digest)


if __name__ == '__main__':
    check_qr_arithmetic()
    check_row_pattern_bound()
    verify()
