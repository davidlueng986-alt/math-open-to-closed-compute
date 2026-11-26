"""Exclude words up to three physical flips from the period-23 shape."""

from collections import Counter
from functools import cache
from itertools import combinations
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from r_paley_periodic_partner import (
    N, centered, choose_columns, dot, elimination, full_column_solver,
    integer_rows, matvec, reflection_data, residue_vectors,
)
from r_paley_far_periodic import raw_word, row_fibres
from verify import goethals_seidel, length_299_words, rows_from_columns


def symmetric(g, reflect, pair_rows, center, eligible, run):
    remaining = [j for j in (*pair_rows, *center) if j not in eligible]

    def orbit(j):
        return (j,) if j == reflect[j] else (j, reflect[j])

    matrix = [tuple(sum(row[k] for k in orbit(j)) for j in remaining) for row in g]
    solvers = [full_column_solver(matrix, p) for p in (13, 23)]
    mapping = []
    for j in eligible:
        rhs = tuple(-sum(row[k] for k in orbit(j)) for row in g)
        a, b = (solve(rhs) for solve in solvers)
        mapping.append(tuple((92 * x + 208 * y) % 299 for x, y in zip(a, b, strict=True)))
    weights = tuple(len(orbit(j)) for j in remaining)
    assert max(sum(abs(v) for v in col) for col in zip(*g)) == 276
    output = run("symmetric", integer_rows([weights, *mapping]))
    assert output[-1] == "profiles 264065"
    for line in output[:-1]:
        tag, *values = line.split()
        assert tag == "hit"
        deck = tuple(map(int, values))
        tail = [centered(dot(deck, row), 299) for row in zip(*mapping)]
        full = [0] * N
        for j, v in zip([*eligible, *remaining], [*deck, *tail], strict=True):
            for k in orbit(j):
                full[k] = v
        assert max(map(abs, full)) <= 69 and dot(full, full) == 6877
        assert any(abs(v) != 299 for v in matvec(g, full))
    print("Paley near-periodic partner: 264065 symmetric decks, no sign precursor")


def sparse_decks(size, budget):
    if size == 0:
        yield ()
        return
    width = min(2, budget)
    for first in range(-width, width + 1):
        for tail in sparse_decks(size - 1, budget - abs(first)):
            yield (first, *tail)


def odd_axes(d, f, g, reflect, pair_rows, eligible):
    def half_difference(matrix):
        return [tuple((matrix[i][j] - matrix[reflect[i]][j]) // 2 for j in pair_rows)
                for i in pair_rows]

    h0 = [tuple(x + y for x, y in zip(row, other, strict=True))
          for row, other in zip(d, f, strict=True)]
    h1 = [tuple(x - y for x, y in zip(row, other, strict=True))
          for row, other in zip(d, f, strict=True)]
    u, v, a = (half_difference(matrix) for matrix in (h0, h1, g))
    columns = tuple(zip(*u))
    n = len(u)
    assert all(dot(x, y) == 23 * (i == j)
               for i, x in enumerate(columns) for j, y in enumerate(columns))
    perm = [tuple(dot(x, y) // 23 for y in zip(*v)) for x in columns]
    assert all(sum(abs(x) for x in row) == 1 for row in perm)
    assert all(perm[i][j] == -perm[j][i] for i in range(n) for j in range(n))
    partners = [next(j for j, value in enumerate(row) if value) for row in perm]
    phases = [2 * perm[i][j] for i, j in enumerate(partners)]
    assert all(a[i][j] == 3 * u[i][j] - phases[j] * u[i][partners[j]]
               for i in range(n) for j in range(n))
    marks = [pair_rows.index(j) for j in eligible]
    assert n == 44 and len(marks) == 24
    ac = tuple(zip(*a))

    @cache
    def recover(residues):
        lifted = []
        for z in residue_vectors(residues, 1012):
            b = matvec(u, z)
            assert all(v % 23 == 0 for v in b)
            if max(map(abs, b)) <= 23 and any(b):
                word = tuple(v // 23 for v in b)
                lifted.append((word, matvec(ac, word)))
        return tuple(lifted)

    words = set()
    for h in range(3):
        profiles = modulus_hits = norm_hits = lifts = 0
        for omitted in combinations(marks, h):
            select = [j for j in marks if j not in omitted]
            complement = [j for j in range(n) if j not in select]
            live = [j for j in select if partners[j] not in select]
            assert len(live) <= 8
            cols = len(complement)
            matrix, pivots = elimination(choose_columns(a, complement), 23, track=True)
            frees = [j for j in range(cols) if j not in pivots]
            assert len(frees) <= 1
            rank = len(pivots)
            reduced = [tuple(-dot(row[cols:], ac[j]) % 23 for j in live) for row in matrix]
            kernel = [0] * n
            if frees:
                free = frees[0]
                kernel[complement[free]] = 1
                for row, piv in zip(matrix[:rank], pivots, strict=True):
                    kernel[complement[piv]] = -row[free] % 23

            for w in sparse_decks(len(live), (37 - 13 * h) // 4):
                profiles += 1
                if any(dot(row, w) % 23 for row in reduced[rank:]):
                    continue
                modulus_hits += 1
                alpha = [0] * n
                for j, value in zip(live, w, strict=True):
                    alpha[j] = value
                for piv, row in zip(pivots, reduced[:rank], strict=True):
                    alpha[complement[piv]] = dot(row, w) % 23

                measured = tuple(alpha[j] for j in select)
                for t in range(23 if frees else 1):
                    projection = tuple(x + t * y for x, y in zip(alpha, kernel, strict=True))
                    residues = tuple(centered(16 * (3 * projection[i] +
                                                   phases[i] * projection[j]), 23)
                                     for i, j in enumerate(partners))
                    if dot(residues, residues) > 1012:
                        continue
                    norm_hits += 1
                    for b, deck in recover(residues):
                        if tuple(deck[j] for j in select) != measured:
                            continue
                        lifts += 1
                        sign = next(v for v in b if v)
                        words.add(tuple(v * sign for v in b))

        expected = [(14025, 25, 5, 28, 14), (249768, 10758, 1718, 696, 26),
                    (31440, 29316, 3496, 8318, 45)]
        assert (profiles, modulus_hits, norm_hits, lifts, len(words)) == expected[h]
    assert all(dot(word, word) == 23 for word in words)
    axis_lines = {tuple(v * next(z for z in row if z) for v in row) for row in columns}
    assert len(axis_lines) == 44 and axis_lines <= words
    print("Paley near-periodic partner: 45 odd lines, all of support 23")
    projection = tuple(zip(*choose_columns(a, marks)))
    return [(word, matvec(projection, word)) for word in sorted(words)]


def mixed(g, reflect, pair_rows, center, eligible, directions, run):
    marks = [*eligible, 57]
    blocks = []
    for odd, deck in directions:
        rows = [tuple(g[i][j] + g[reflect[i]][j] for j in marks)
                for i, v in zip(pair_rows, odd, strict=True) if not v]
        rows.extend(tuple(g[i][j] for j in marks) for i in center)
        assert len(rows) == 25
        blocks.append(integer_rows([(len(rows),), deck, *rows]))
    output = run("mixed", str(len(directions)) + "\n" + "".join(blocks))
    assert output == ["matched 13342818 records 0"]
    print("Paley near-periodic partner: 13342818 exact split keys, no one-flip precursor")



def physical_flips(g, run):
    source = goethals_seidel(length_299_words())
    height = len(source)
    fibres = row_fibres()
    anchor = raw_word(source, fibres)
    rows = rows_from_columns(height, source)
    eligible = {j for j, col in enumerate(source) if abs(height - 2 * (anchor ^ col).bit_count()) == 2}
    classes = [i for i, fibre in enumerate(fibres) if fibre[0] in eligible]
    assert len(classes) == 49 and len(eligible) == 637
    assert eligible == {j for i in classes for j in fibres[i]}
    fibre_masks = [sum(1 << j for j in fibres[i]) for i in classes]
    mask = sum(fibre_masks)
    physical_type = {r: i for i, fibre in enumerate(fibres) for r in fibre}
    selected = choose_columns(g, classes)
    for r, row in enumerate(rows):
        assert selected[physical_type[r]] == tuple(2 * (row & m).bit_count() - 13
                                                  for m in fibre_masks)
    imbalance = [
        [[sum(abs(a + phase * b) for a, b in zip(left, right, strict=True))
          for right in selected] for left in selected]
        for phase in (1, -1)
    ]

    losses = Counter()
    witnesses = {}
    for r, s in combinations(range(height), 2):
        i, j = physical_type[r], physical_type[s]
        corr = 637 - 2 * ((rows[r] ^ rows[s]) & mask).bit_count()
        for k, phase in enumerate((1, -1)):
            if phase < 0 and i == j:
                continue
            bias = imbalance[k][i][j]
            value = 637 + phase * corr - bias
            assert value >= 0 and value % 4 == 0
            failure = value // 4
            losses[failure] += 1
            witnesses.setdefault(failure, (r, s, phase, phase * corr, bias))
    assert sum(losses.values()) == 1422044 and min(losses) == 71
    assert losses[71] == 26 and witnesses[71] == (607, 676, 1, -31, 322)
    print("Paley near-periodic partner: 1422044 two-flip phases, at least 71 lost projections")

    encoded = integer_rows(
        (physical_type[r], *(sum(((row >> col) & 1) << bit for bit, col in enumerate(fibres[i]))
                             for i in classes))
        for r, row in enumerate(rows)
    )
    output = run("triples", encoded)
    assert output == ["triples 1120601768 minimum 63 ties 6"]
    print("Paley near-periodic partner: 1120601768 three-flip phases, at least 63 lost projections")


def verify():
    d, f, g, _, reflect, pair_rows, center, eligible = reflection_data()
    with TemporaryDirectory() as temp:
        exe = Path(temp) / "near-periodic-partner"
        worker = Path(__file__).with_suffix(".cpp")
        subprocess.run(["g++", "-O3", "-std=c++17", str(worker), "-o", str(exe)], check=True)

        def run(mode, inp):
            return subprocess.run([str(exe), mode], input=inp, text=True, check=True,
                                  capture_output=True).stdout.strip().splitlines()

        symmetric(g, reflect, pair_rows, center, eligible, run)
        directions = odd_axes(d, f, g, reflect, pair_rows, eligible)
        mixed(g, reflect, pair_rows, center, eligible, directions, run)
        physical_flips(g, run)


if __name__ == "__main__":
    verify()
