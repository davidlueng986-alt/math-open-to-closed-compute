"""Replay a larger Paley inner family and six exact periodic-frame obstructions."""

from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from r_paley_projective_lift import build
from verify import goethals_seidel, length_299_words, rows_from_columns, verify_orthogonal


T = 599
SOURCE_ORDER = 2*T-2
PERIOD = 299
DATA = Path(__file__).with_name('r_paley_periodic_skew_data.json')


def coordinate(block, residue13, residue23):
    return block*PERIOD + residue13 + 13*((residue23-residue13)*16 % 23)


def sign(column, row):
    return 2*(column >> row & 1)-1


def check_frame(source, rows, reserves):
    assert len(rows) == len(set(rows)) == len(reserves) == len(set(reserves))
    orientation = [sign(source[c], r) for r,c in zip(rows, reserves, strict=True)]
    assert all(sign(source[reserves[i]], rows[j])*orientation[i]
               == -sign(source[reserves[j]], rows[i])*orientation[j]
               for i,j in combinations(range(len(rows)), 2))


def check_prime_cut(source, record):
    shift, residue_lists = record['shift'], record['residues']
    assert shift in (3, 9) and len(residue_lists) == 4
    rows = [coordinate(block, r, 11) for block,residues in enumerate(residue_lists) for r in residues]
    reserve = [coordinate(block, (r+shift)%13, 11)
               for block,residues in enumerate(residue_lists) for r in residues]
    assert len(rows) == 24
    check_frame(source, rows, reserve)
    weights = tuple(int(x, 16) for x in record['proof'])
    assert len(weights) == 276 and all(0 <= w < 13 for w in weights)
    pairs = [(rows[i], rows[j], w) for (i,j),w in zip(combinations(range(24), 2), weights, strict=True) if w]
    assert all(sum(w*sign(col, i)*sign(col, j) for i,j,w in pairs)%13 == 1 for col in source)
    assert (T+1)%13 == 2


def check_extension(source, record):
    rows, reserves, selected = record['inner_rows'], record['inner_columns'], record['w_columns']
    gamma = record['gamma_index']
    k = len(rows)
    if 'residues' in record:
        groups = record['residues']
        assert k == sum(map(len, groups)) and len(groups) == 4
        assert rows == [coordinate(b, 7, r) for b,S in enumerate(groups) for r in S]
        assert reserves == [coordinate(b, 6, (r+2)%23) for b,S in enumerate(groups) for r in S]
    check_frame(source, rows, reserves)
    assert len(selected) == T and len(set(selected)|{gamma, *reserves}) == T+1+k
    source_indices = [gamma, *selected]
    assert all(0 <= i < SOURCE_ORDER for i in (*rows, *reserves, *source_indices))
    projections = rows_from_columns(SOURCE_ORDER, [source[i] for i in source_indices])
    support = [projections[r] for r in rows]
    assert all((a^b).bit_count() == (T+1)//2 for a,b in combinations(support, 2))
    flipped = [c for r,c in zip(rows,reserves,strict=True) if sign(source[c], r) != sign(source[gamma], r)]
    assert flipped == record['flipped_source_columns']
    source = list(source)
    for c in flipped:
        source[c] ^= (1 << SOURCE_ORDER)-1
    outside, inside = build(T, source, zip(rows,reserves,strict=True), selected, gamma)
    cols = outside + inside
    assert len(cols) == record['width'] == 2*T+2+k
    pairs = verify_orthogonal(4*T, cols)
    assert pairs == record['pair_count']
    digest = sha256(b''.join(c.to_bytes((4*T+7)//8, 'little') for c in cols)).hexdigest()
    assert digest == record['sha256']
    print(f'Hadamard 2396 × {len(cols)}: {k} compatible inner candidates, all {pairs} pair products zero, SHA256 {digest}')
    return rows, reserves, source_indices


def histogram(source, rows, indices):
    return Counter(tuple(sign(source[c], r)*sign(source[c], rows[0]) for r in rows[1:])
                   for c in indices)


def verify():
    data = json.loads(DATA.read_text(encoding='ascii'))
    source = goethals_seidel(length_299_words())
    assert verify_orthogonal(SOURCE_ORDER, source) == 714610
    cases = data['mod13']
    assert len(cases) == 6
    assert len({(d['shift'],tuple(map(tuple,d['residues']))) for d in cases}) == len(cases)
    for record in cases:
        check_prime_cut(source,record)
    print('Paley periodic frame: six 24-row skew frames require selected width divisible by 13')
    previous = None
    for record in data['extensions']:
        rows, reserves, selected = check_extension(source, record)
        if previous is not None:
            old_rows, old_reserves, old_selected = previous
            assert rows[:-1] == old_rows and reserves[:-1] == old_reserves
            assert histogram(source, old_rows, selected) == histogram(source, old_rows, old_selected)
            print(f'Added source row {rows[-1]}, reserve {reserves[-1]}, preserving all 600 old-row profiles')
        previous = (rows, reserves, selected)


if __name__ == '__main__':
    verify()
