"""Rebuild compatible outside and inside columns from several raw row flips."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from r_paley_projective_lift import build
from stack_1198_joint import dot
from verify import goethals_seidel, length_299_words, rows_from_columns, verify_orthogonal


T = 599
SIDE = 2 * T - 2
ORDER = 4 * T


def replay(source, fixture):
    stock = set(fixture['K'])
    assert len(stock) == len(fixture['K']) == T + 1
    gamma, *chosen = fixture['K']
    assert 0 <= min(stock) and max(stock) < SIDE
    raw, selected_projections, nonflip = [], [], 0
    for entry in fixture['inner']:
        pivot, positions = entry['pivot'], entry['positions']
        assert 0 <= pivot < SIDE and len(positions) == len(set(positions))
        assert len(positions) % 2 == 1 and all(0 <= r < SIDE for r in positions)
        changed = source[pivot] ^ sum(1 << r for r in positions)
        assert min(min((changed ^ col).bit_count(), SIDE - (changed ^ col).bit_count())
                   for col in source) == len(positions)
        deck = [dot(SIDE, changed, col) for col in source]
        eligible = {j for j, p in enumerate(deck) if abs(p) == 2}
        assert len(eligible) == entry['eligible'] and stock <= eligible
        flip_sign = (-1) ** ((len(positions) + 1) // 2)
        for j in stock:
            minus = sum(((source[pivot] ^ source[j]) >> r) & 1 for r in positions)
            assert deck[j] // 2 == flip_sign * (-1) ** minus
        raw.append(changed)
        selected_projections.append(tuple(deck[j] // 2 for j in fixture['K']))
        nonflip += len(positions) > 1

    assert nonflip == fixture['nonflip']
    assert Counter(dot(SIDE, a, b) for a, b in combinations(raw, 2)) == {
        int(value): count for value, count in fixture['raw_lower_products'].items()
    }
    for (a, u), (b, v) in combinations(zip(raw, selected_projections, strict=True), 2):
        assert dot(SIDE, a, b) + 2 * sum(x * y for x, y in zip(u, v, strict=True)) == 0

    outside, inside = build(T, source, (), chosen, gamma)
    mask = (1 << SIDE) - 1
    top_mask = (1 << T) - 1
    for word, (projection_gamma, *projections) in zip(raw, selected_projections, strict=True):
        orientation = -projection_gamma
        z = mask ^ source[gamma] ^ word
        if orientation < 0:
            z ^= mask
        assert z.bit_count() == T - 2
        top = sum(int(p * orientation == -1) << j for j, p in enumerate(projections))
        inside.append(top | ((top ^ top_mask) << T) | (z << (2 * T)) | (3 << (ORDER - 2)))

    columns = outside + inside
    assert len(outside) == 1198 and len(columns) == fixture['width']
    orthogonal_pairs = verify_orthogonal(ORDER, columns)
    assert orthogonal_pairs == len(columns) * (len(columns) - 1) // 2
    mask = (1 << (ORDER - 2)) - 1
    exterior = [col & mask for col in outside]
    blocks = rows_from_columns(ORDER - 2, exterior)
    assert len(set(blocks)) == ORDER - 2 and all(word.bit_count() == T for word in blocks)
    assert all((a & b).bit_count() == T - 1 for a, b in combinations(exterior, 2))
    digest = sha256(b''.join(word.to_bytes((ORDER + 7) // 8, 'little') for word in columns)).hexdigest()
    return orthogonal_pairs, digest


def verify():
    source = goethals_seidel(length_299_words())
    assert verify_orthogonal(SIDE, source) == 714610
    data = Path(__file__).with_name('r_paley_multiflip_inner_data.json')
    for record in json.loads(data.read_text(encoding='ascii')):
        pairs, digest = replay(source, record)
        assert digest == record['sha256']
        print(f"Paley multiflip: {ORDER} x {record['width']}, {record['nonflip']} non-one-flip columns, "
              f"{pairs} exact products, SHA256 {digest}")


if __name__ == '__main__':
    verify()
