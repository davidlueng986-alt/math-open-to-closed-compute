"""Rebuild an exact Paley exterior with a chosen skew inner submatrix."""

from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from r_paley_projective_lift import build
from stack_1198_joint import dot
from verify import goethals_seidel, length_299_words, rows_from_columns, verify_orthogonal


def check_square_control():
    source = (15, 5, 3, 9)
    t = 3
    outside, inner = build(t, source, (), w_columns=(1, 2, 3), gamma_index=0)
    bottom = (1, 2, 4, 8)  # columns of 2I - J written as sign words
    assert verify_orthogonal(4, bottom) == 6
    for z in bottom:
        assert z.bit_count() == 1 and all(abs(dot(4, w, z)) == 2 for w in source[1:])
        u = sum((dot(4, w, z) == -2) << j for j, w in enumerate(source[1:]))
        inner.append(u | ((u ^ 7) << t) | (z << (2*t)) | (3 << 10))
    assert len(outside + inner) == 12 and verify_orthogonal(12, outside + inner) == 66


def check_symmetric_core():
    source = tuple(sum((1 - (i & j).bit_count() % 2) << i for i in range(8)) for j in range(8))
    outside, inside = build(5, source, ((0, 6),))
    assert len(outside + inside) == 13 and verify_orthogonal(20, outside + inside) == 78


def verify():
    check_square_control()
    check_symmetric_core()
    t = 599
    height, order = 2*t - 2, 4*t
    source = goethals_seidel(length_299_words())
    assert verify_orthogonal(height, source) == 714610
    path = Path(__file__).with_name('r_paley_skew_inner_data.json')
    record = json.loads(path.read_text(encoding='ascii'))
    chosen = record['w_columns']
    rows, reserve = record['inner_rows'], record['inner_columns']
    assert len(chosen) == len(set(chosen)) == t
    assert len(rows) == len(set(rows)) == len(set(reserve)) == len(reserve)
    assert set(chosen).isdisjoint({0, *reserve}) and 0 not in reserve
    assert all(0 <= i < height for i in (*chosen, *rows, *reserve))
    mask = (1 << height) - 1
    normalized = [mask ^ source[0] ^ col for col in source]
    w = rows_from_columns(height, [normalized[i] for i in chosen])
    for i, r in enumerate(rows):
        assert (normalized[reserve[i]] >> r) & 1
    for i, j in combinations(range(len(rows)), 2):
        r, s = rows[i], rows[j]
        assert dot(t, w[r], w[s]) == -1
        assert ((normalized[reserve[j]] >> r) ^ (normalized[reserve[i]] >> s)) & 1
    outside, inside = build(t, source, zip(rows, reserve, strict=True), chosen, gamma_index=0)
    columns = outside + inside
    assert len(outside) == 2*t and len(inside) == len(rows)+2
    assert len(columns) == record['width']
    assert verify_orthogonal(order, columns) == record['pairs'] == len(columns)*(len(columns)-1)//2
    digest = sha256(b''.join(col.to_bytes((order+7)//8, 'little') for col in columns)).hexdigest()
    assert digest == record['sha256']
    print(f'Chosen skew rows: H partial {order} × {len(columns)}, all {record["pairs"]} products exact, SHA256 {digest}')


if __name__ == '__main__':
    verify()
