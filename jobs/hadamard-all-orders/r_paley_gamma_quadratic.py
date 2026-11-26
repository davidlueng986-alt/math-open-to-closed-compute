"""Verify 2396 reserve-axis exclusions and recover the full reserve CRT map."""

from argparse import ArgumentParser
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
T, D, CHOSEN, RESERVE = 599, 299, 600, 596
HEIGHT = CHOSEN + RESERVE
CRT_ROWS = RESERVE + 2


def source_data():
    source = goethals_seidel(length_299_words())
    previous = next(row for row in json.loads(PERIODIC_DATA.read_text(encoding='ascii'))['extensions']
                    if row['width'] == 1214)
    rows = previous['inner_rows'] + [319]
    pivots = previous['inner_columns'] + [344]
    chosen = [j for j in range(HEIGHT) if SELECTED >> j & 1]
    unused = [j for j in range(HEIGHT) if not SELECTED >> j & 1]
    assert len(chosen) == CHOSEN and len(unused) == RESERVE
    anchors = [reserve_unit(source, unused, row, pivot)
               for row, pivot in zip(rows, pivots, strict=True)]
    units = [q for _, _, _, q in anchors]
    positions = [unused.index(pivot) for pivot in pivots]
    for index, word in json.loads(DATA.read_text(encoding='ascii')):
        mask = int(word, 16)
        assert 0 <= index < RESERVE and mask >> RESERVE == 0 and mask >> index & 1
        unit = list(signs(mask, RESERVE))
        unit[index] = 2
        units.append(unit)
        positions.append(index)
    assert len(units) == len(set(positions)) == 29
    assert all(dot(q, r) == T*(i == j)
               for i, q in enumerate(units) for j, r in enumerate(units))
    assert all(dot(q, w) % T == 0 for q in units for _, _, w, _ in anchors)
    assert len(reduced_rows(units, T)[1]) == 29
    coefficients = [tuple(dot(q, w)//T for _, _, w, _ in anchors) for q in units]
    assert all(abs(x) == 1 for row in coefficients for x in row)
    columns = tuple(zip(*coefficients, strict=True))
    assert max(sum(abs(dot(a, b)) for b in columns) for a in columns) == 93
    print('Reserve units: exact Gram, mod-599 rank 29, and residual Gram bound 503 verified', flush=True)

    selected_rows = rows_from_columns(HEIGHT, [source[j] for j in chosen])
    reserve_rows = rows_from_columns(HEIGHT, [source[j] for j in unused])
    selected_words = [tuple(projections[j] for j in chosen) for _, projections, _, _ in anchors]
    return anchors, units, positions, selected_words, selected_rows, reserve_rows


def kernel_input(units, positions, selected_words, selected_rows, reserve_rows):
    unit_signs = [sum((value > 0) << i for i, value in enumerate(q)) for q in units]
    lines = [' '.join(map(str, selected_words[0]))]
    for top, bottom in zip(selected_rows, reserve_rows, strict=True):
        image = [RESERVE - 2*(bottom ^ word).bit_count() + sign(bottom, j)
                 for word, j in zip(unit_signs, positions, strict=True)]
        lines.append(' '.join(map(str, (*signs(top, CHOSEN), *image))))
    lines.extend(' '.join(map(str, signs(bottom, RESERVE))) for bottom in reserve_rows)
    return '\n'.join(lines) + '\n'


def read_crt_maps(path):
    """Read the p=13,23 maps, each with 596 reserve rows then two check rows."""
    data = path.read_bytes()
    width = CRT_ROWS * CHOSEN
    assert len(data) == 2*width
    fields = []
    for index, prime in enumerate((13, 23)):
        block = data[index*width:(index+1)*width]
        assert max(block) < prime
        fields.append(tuple(block[j:j+CHOSEN] for j in range(0, width, CHOSEN)))
    return tuple(fields)


def centered_reserve(fields, selected):
    """Return centered r for the congruence X a + V r = 0 (mod 299)."""
    residues = []
    for field, prime in zip(fields, (13, 23), strict=True):
        if any(dot(row, selected) % prime for row in field[RESERVE:]):
            return None
        residues.append(tuple(-dot(row, selected) % prime for row in field[:RESERVE]))
    return tuple((92*a + 208*b + 149) % D - 149
                 for a, b in zip(*residues, strict=True))


def weighted_word(values, row):
    return sum(weight*((row & positives).bit_count() - ((~row) & positives).bit_count()
                      - (row & negatives).bit_count() + ((~row) & negatives).bit_count())
               for weight, (positives, negatives) in values.items())


def weight_masks(column):
    return {weight: (sum((x == weight) << j for j, x in enumerate(column)),
                     sum((x == -weight) << j for j, x in enumerate(column)))
            for weight in {abs(x) for x in column if x}}


def check_lift_bounds():
    off_pivot_norm = max(T*s - (s+p)**2 for s in range(299) for p in (0, 1))
    noncentral_minimum = (D+1)//2
    assert off_pivot_norm == 89698 < 4*noncentral_minimum**2
    assert off_pivot_norm < (D+1)**2
    assert off_pivot_norm - D**2 == 297 < noncentral_minimum**2
    print('Full CRT bound: at most three off-pivot corrections and four in all')


def check_controls(fields, anchors, units, positions, selected_words, selected_rows, reserve_rows):
    base_word, _, w0, _ = anchors[0]
    b0 = selected_words[0]
    assert all(abs(x) == 1 for b in selected_words for x in b)
    forced = units[:15]
    epsilons = [dot(q, w0)//T for q in forced]
    assert set(map(abs, epsilons)) == {1}
    corrections = set()
    for anchor_id, ((word, _, w, _), b) in enumerate(zip(anchors[1:], selected_words[1:], strict=True), 1):
        for orientation in (-1, 1):
            a = tuple((x-orientation*y)//2 for x, y in zip(b0, b, strict=True))
            r = tuple((x-orientation*y)//2 for x, y in zip(w0, w, strict=True))
            assert dot(a, a) == 300 and dot(r, r) == T*298
            u = centered_reserve(fields, a)
            assert u is not None and all((x-y) % D == 0 for x, y in zip(r, u, strict=True))
            delta = tuple((x-y)//D for x, y in zip(r, u, strict=True))
            assert set(map(abs, delta)) <= {0, 1} and dot(delta, delta) <= 4
            g0 = positions[0]
            off_pivot = [j for j, d in enumerate(delta) if j != g0 and d]
            assert len(off_pivot) <= 3 and dot(r, r) - r[g0]**2 <= 89698
            assert all(delta[j]*u[j] <= 0 for j in off_pivot)
            assert all(u[j] or len(off_pivot) == 1 for j in off_pivot)
            corrections.add((dot(delta, delta), len(off_pivot)))
            assert dot(r, r) == dot(u, u) + sum(D*D+2*D*x*y for x, y in zip(u, delta, strict=True) if y)
            for i, (q, epsilon, b_i, g_i) in enumerate(zip(forced, epsilons, selected_words, positions[:15], strict=True)):
                raw = dot(q, u)
                assert raw % D in (0, epsilon % D)
                p = epsilon if raw % D else 0
                assert raw + D*dot(q, delta) == T*p and abs(dot(q, delta)) <= 5
                target = 2*D*((i == 0) - orientation*(i == anchor_id))
                assert r[g_i] == target - dot(a, b_i) + p

            chosen_masks, center_masks = weight_masks(a), weight_masks(u)
            correction_masks = weight_masks(delta)
            for i, (top, bottom) in enumerate(zip(selected_rows, reserve_rows, strict=True)):
                value = weighted_word(chosen_masks, top) + weighted_word(center_masks, bottom)
                assert value % D == 0
                observed = sign(base_word, i) - value//D - weighted_word(correction_masks, bottom)
                assert observed == orientation*sign(word, i)
    print(f'Full CRT lift: 28 exact known root controls, (total, off pivot) corrections {sorted(corrections)}')


def verify(write_crt):
    anchors, units, positions, selected_words, selected_rows, reserve_rows = source_data()
    source = Path(__file__).with_suffix('.cpp')
    data = kernel_input(units, positions, selected_words, selected_rows, reserve_rows)
    with TemporaryDirectory() as directory:
        binary, maps = (Path(directory) / name for name in ('gamma_quadratic', 'crt_maps.bin'))
        run(['g++', '-O3', '-std=c++20', str(source), '-o', str(binary)], check=True)
        run([str(binary), str(maps)], input=data, text=True, check=True)
        check_lift_bounds()
        check_controls(read_crt_maps(maps), anchors, units, positions, selected_words, selected_rows, reserve_rows)
        if write_crt is not None:
            write_crt.write_bytes(maps.read_bytes())


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--write-crt', type=Path, help='write the verified two-field map to a binary file')
    verify(parser.parse_args().write_crt)
