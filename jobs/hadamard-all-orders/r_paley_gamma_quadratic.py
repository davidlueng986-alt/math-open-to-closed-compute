"""Verify quadratic exclusions for two explicit 2396 reserve-axis spans."""

import json
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from r_paley_bucket_extension import SELECTED
from r_paley_gamma_splitting import reserve_unit, sign
from r_paley_isotropic_code import dot
from r_paley_lattice_lift import signs
from r_paley_order44_classifier import reduced_rows
from r_paley_periodic_skew import DATA as PERIODIC_DATA
from verify import goethals_seidel, length_299_words, rows_from_columns


DATA = Path(__file__).with_name('r_paley_gamma_quadratic_data.json')


def kernel_input():
    t, m, v = 599, 1196, 596
    source = goethals_seidel(length_299_words())
    previous = next(row for row in json.loads(PERIODIC_DATA.read_text(encoding='ascii'))['extensions']
                    if row['width'] == 1214)
    rows = previous['inner_rows'] + [319]
    pivots = previous['inner_columns'] + [344]
    chosen = [j for j in range(m) if SELECTED >> j & 1]
    unused = [j for j in range(m) if not SELECTED >> j & 1]
    assert len(chosen) == 600 and len(unused) == v
    anchors = [reserve_unit(source, unused, row, pivot)
               for row, pivot in zip(rows, pivots, strict=True)]
    units = [q for _, _, _, q in anchors]
    positions = [unused.index(pivot) for pivot in pivots]
    for index, word in json.loads(DATA.read_text(encoding='ascii')):
        mask = int(word, 16)
        assert 0 <= index < v and mask >> v == 0 and mask >> index & 1
        unit = list(signs(mask, v))
        unit[index] = 2
        units.append(unit)
        positions.append(index)
    assert len(units) == len(set(positions)) == 19
    assert all(dot(q, r) == t*(i == j)
               for i, q in enumerate(units) for j, r in enumerate(units))
    assert all(dot(q, w) % t == 0 for q in units for _, _, w, _ in anchors)
    assert len(reduced_rows(units, t)[1]) == 19
    print('Reserve units: exact Gram, old-code orthogonality and mod-599 independence verified', flush=True)

    b = [anchors[0][1][j] for j in chosen]
    selected_rows = rows_from_columns(m, [source[j] for j in chosen])
    reserve_rows = rows_from_columns(m, [source[j] for j in unused])
    unit_signs = [sum((value > 0) << i for i, value in enumerate(q)) for q in units]
    matrix = [' '.join(map(str, b))]
    for top, bottom in zip(selected_rows, reserve_rows, strict=True):
        image = [v - 2*(bottom ^ word).bit_count() + sign(bottom, j)
                 for word, j in zip(unit_signs, positions, strict=True)]
        matrix.append(' '.join(map(str, (*signs(top, len(chosen)), *image))))
    return '\n'.join(matrix) + '\n'


def verify():
    source = Path(__file__).with_suffix('.cpp')
    data = kernel_input()
    with TemporaryDirectory() as directory:
        binary = Path(directory) / 'gamma_quadratic'
        run(['g++', '-O3', '-std=c++20', str(source), '-o', str(binary)], check=True)
        run([str(binary)], input=data, text=True, check=True)


if __name__ == '__main__':
    verify()
