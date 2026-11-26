"""Exact exclusion of a period-23 partner of the published far word."""

from math import isqrt
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from r_paley_periodic_weighing import data, dot, gram_check

N = 92
SIDE = 44
P = (13, 23)


def matvec(matrix, vector):
    return tuple(dot(row, vector) for row in matrix)


def identity(n):
    return [tuple(int(i == j) for j in range(n)) for i in range(n)]


def elimination(matrix, prime, track=False):
    height, width = len(matrix), len(matrix[0])
    rows = [list(row) for row in matrix]
    if track:
        for row, unit in zip(rows, identity(height), strict=True):
            row.extend(unit)
    rows = [[v % prime for v in row] for row in rows]
    pivots = []
    rank = 0
    for col in range(width):
        index = next((i for i in range(rank, height) if rows[i][col]), None)
        if index is None:
            continue
        rows[index], rows[rank] = rows[rank], rows[index]
        inv = pow(rows[rank][col], -1, prime)
        pivot = [v * inv % prime for v in rows[rank]]
        rows[rank] = pivot
        for j, row in enumerate(rows):
            if j != rank and row[col]:
                c = row[col]
                rows[j] = [(a - c * b) % prime for a, b in zip(row, pivot, strict=True)]
        pivots.append(col)
        rank += 1
    return rows, pivots


def null_checks(matrix, prime):
    rows, pivots = elimination(matrix, prime)
    checks = []
    for j in range(len(matrix[0])):
        if j in pivots:
            continue
        word = [int(k == j) for k in range(len(matrix[0]))]
        for row, pos in zip(rows[:len(pivots)], pivots, strict=True):
            word[pos] = -row[j] % prime
        assert all(x % prime == 0 for x in matvec(matrix, word))
        checks.append((prime, tuple(word)))
    return checks


def full_column_solver(matrix, prime):
    width = len(matrix[0])
    rows, pivots = elimination(matrix, prime, track=True)
    assert pivots == list(range(width))
    transform = [tuple(row[width:]) for row in rows]

    def solve(rhs):
        reduced = tuple(v % prime for v in matvec(transform, rhs))
        assert not any(reduced[width:])
        ans = reduced[:width]
        assert all((x - y) % prime == 0 for x, y in zip(matvec(matrix, ans), rhs, strict=True))
        return ans

    return solve


def choose_columns(matrix, cols):
    return [tuple(row[j] for j in cols) for row in matrix]


def centered(x, p):
    return (x + p // 2) % p - p // 2


def nary(code, base, length):
    return tuple(code // base**j % base for j in range(length))


def minus_plus(number, length):
    return tuple(2 * x - 1 for x in nary(number, 2, length))


def integer_rows(rows):
    return "\n".join(" ".join(map(str, row)) for row in rows) + "\n"


def reflection_data():
    d, f, g, raw = data()
    reflect = tuple(j // 23 * 23 + 22 - j % 23 for j in range(N))
    pair_rows = tuple(j for j in range(N) if j < reflect[j])
    center = tuple(range(11, N, 23))
    assert len(pair_rows) == SIDE and len(center) == 4
    assert all(g[i][j] == g[reflect[i]][reflect[j]] for i in range(N) for j in range(N))
    assert raw == tuple(raw[j] for j in reflect)
    deck = matvec(tuple(zip(*g)), raw)
    eligible = [j for j in pair_rows if abs(deck[j]) == 2]
    assert len(eligible) == 24 and [j for j in center if abs(deck[j]) == 2] == [57]
    return d, f, g, raw, reflect, pair_rows, center, eligible


def symmetric_phase(g, raw, reflect, pair_rows, center, eligible, run):
    # Half-projections on the known 24 reflected pairs determine all others
    # modulo 299 by the two prime-field solves.
    unknown = [j for j in (*pair_rows, *center) if j not in eligible]
    def orbit(j):
        return (j, reflect[j]) if j != reflect[j] else (j,)
    matrix = [tuple(sum(row[j] for j in orbit(k)) for k in unknown) for row in g]
    solvers = [full_column_solver(matrix, p) for p in P]
    mapping = []
    for j in eligible:
        rhs = tuple(-sum(row[i] for i in orbit(j)) for row in g)
        v, w = (solver(rhs) for solver in solvers)
        mapping.append(tuple((92 * a + 208 * b) % 299 for a, b in zip(v, w, strict=True)))
    weights = tuple(len(orbit(j)) for j in unknown)
    assert sum(weights) + 2 * len(eligible) == N
    assert max(sum(abs(v) for v in col) for col in zip(*g)) == 276
    output = run("symmetric", integer_rows([weights, *mapping]))
    candidates = []
    for line in output:
        low, high = map(int, line.split())
        given = minus_plus(low, 12) + minus_plus(high, 12)
        unselected = [centered(dot(given, col), 299) for col in zip(*mapping)]
        full = [0] * N
        for j, p in zip([*eligible, *unknown], [*given, *unselected], strict=True):
            for k in orbit(j):
                full[k] = p
        assert all(abs(v) <= 138 and v % 2 for v in full)
        assert dot(full, full) == 27508
        product = matvec(g, full)
        if all(abs(v) == 598 for v in product):
            y = tuple(v // 598 for v in product)
            assert matvec(tuple(zip(*g)), y) == tuple(2 * v for v in full)
            candidates.append(y)
    assert len(output) == len(candidates) == 1
    assert candidates[0] in (raw, tuple(-v for v in raw))
    print("Paley periodic partner: only the original line in the symmetric phase")


def residue_vectors(residues, norm):
    """Visit all integer representatives of a residue word below the norm bound."""
    base = sum(v * v for v in residues)
    if base > norm:
        return
    budget = norm - base
    word = list(residues)
    options = []
    for i, v in enumerate(residues):
        radius = isqrt(v * v + budget)
        low, high = -((radius + v) // 23), (radius - v) // 23
        alternatives = [(v + 23 * k, (v + 23 * k)**2 - v * v)
                        for k in range(low, high + 1)]
        if len(alternatives) > 1:
            options.append((i, alternatives))

    def visit(k, available):
        if k == len(options):
            yield tuple(word)
            return
        i, choices = options[k]
        for value, cost in choices:
            if cost <= available:
                word[i] = value
                yield from visit(k + 1, available - cost)
    yield from visit(0, budget)


def odd_phase(d, f, g, reflect, pair_rows, eligible, run):
    def odd(matrix):
        return [tuple((matrix[i][j] - matrix[reflect[i]][j]) // 2 for j in pair_rows)
                for i in pair_rows]
    u = odd([tuple(a + b for a, b in zip(r, s, strict=True)) for r, s in zip(d, f)])
    v = odd([tuple(a - b for a, b in zip(r, s, strict=True)) for r, s in zip(d, f)])
    a = odd(g)
    uc = tuple(zip(*u))
    assert gram_check(uc, uc, 23)
    signed_permutation = [tuple(dot(c, b) // 23 for b in zip(*v)) for c in uc]
    assert all(sum(abs(x) for x in row) == 1 for row in signed_permutation)
    assert all(sum(abs(x) for x in col) == 1 for col in zip(*signed_permutation))
    assert all(signed_permutation[i][j] == -signed_permutation[j][i]
               for i in range(SIDE) for j in range(SIDE))
    change = [tuple(3 * (i == j) + 2 * signed_permutation[i][j] for j in range(SIDE))
              for i in range(SIDE)]
    assert all(tuple(dot(row, c) for c in zip(*change)) == aa for row, aa in zip(u, a))
    marks = [pair_rows.index(j) for j in eligible]
    omitted = [marks[:i] + marks[i+1:] for i in range(24)]
    systems = []
    solvers = []
    for selected in omitted:
        ac = choose_columns(a, selected)
        checks = sum((null_checks(ac, p) for p in P), [])
        assert [p for p, _ in checks].count(13) in (8, 9)
        assert [p for p, _ in checks].count(23) == 1
        complement = [j for j in range(SIDE) if j not in selected]
        solvers.append((complement, full_column_solver(choose_columns(a, complement), 23)))
        systems.append(checks)
    inp = str(len(systems)) + "\n"
    for S in systems:
        inp += str(len(S)) + "\n" + integer_rows([(p, *c) for p, c in S])
    output = run("odd", inp)
    norm_fail, nonzero = 0, 0
    counts = [0] * 24
    profiles = set()
    max_weight = 0
    for line in output:
        branch, lo, hi = map(int, line.split())
        w = tuple(v - 1 for v in nary(lo, 3, 11) + nary(hi, 3, 12))
        assert (branch, w) not in profiles
        profiles.add((branch, w))
        counts[branch] += 1
        assert all(dot(w, c) % p == 0 for p, c in systems[branch])
        weight = dot(w, w)
        max_weight = max(max_weight, weight)
        if weight == 0:
            continue
        nonzero += 1
        selected = omitted[branch]
        complement, solve = solvers[branch]
        rhs = tuple(-dot(w, [row[k] for k in selected]) for row in a)
        full = [0] * SIDE
        for j, value in zip(selected, w, strict=True):
            full[j] = value
        for j, value in zip(complement, solve(rhs), strict=True):
            full[j] = value
        residues = tuple(centered(16 * v, 23) for v in matvec(change, full))
        if dot(residues, residues) > 1012:
            norm_fail += 1
            continue
        for candidate in residue_vectors(residues, 1012):
            product = matvec(u, candidate)
            assert all(v % 23 == 0 for v in product)
            b = tuple(v // 23 for v in product)
            assert not (max(map(abs, b)) <= 1 and
                        matvec(tuple(zip(*choose_columns(a, selected))), b) == w)
    assert counts == [85,111,85,95,99,91,93,93,111,103,99,77,97,83,93,97,9,13,97,13,11,7,11,93]
    assert len(profiles) == 1766 and nonzero == 1742 and norm_fail == 1492 and max_weight == 7

    # For a zero deck, the same mod-23 solve shows every coordinate of
    # U^T b divisible by 23. Its norm bound permits just one signed axis.
    axes = []
    selected = choose_columns(a, marks)
    for axis in uc:
        deck = matvec(tuple(zip(*selected)), axis)
        if sum(v != 0 for v in deck) <= 1:
            axes.append((axis, deck))
    assert len(axes) == 26
    print("Paley periodic partner: 1766 odd decks, only 26 nonzero odd lines survive")
    return axes


def even_phase(g, reflect, pair_rows, center, eligible, axes, run):
    cases = []
    for axis, deck in axes:
        rows = [tuple(g[i][j] + g[reflect[i]][j] for j in eligible)
                for i, value in zip(pair_rows, axis, strict=True) if value == 0]
        rows += [tuple(g[i][j] for j in eligible) for i in center]
        assert len(rows) == 25
        target = tuple(2 if v == 0 else 0 if abs(v) == 1 else -1 for v in deck)
        cases.append(integer_rows([(len(rows),), target, *rows]))
    output = run("even", str(len(cases)) + "\n" + "".join(cases))
    assert output == ["matched 272754"]
    print("Paley periodic partner: 272754 exact split keys, no distinct periodic partner")


def verify():
    d, f, g, raw, reflect, pair_rows, center, eligible = reflection_data()
    with TemporaryDirectory() as tmp:
        exe = Path(tmp) / "periodic-partner"
        worker = Path(__file__).with_suffix(".cpp")
        subprocess.run(["g++", "-O3", "-std=c++17", str(worker), "-o", str(exe)], check=True)

        def run(mode, inp):
            return subprocess.run([str(exe), mode], input=inp, text=True, check=True,
                                  capture_output=True).stdout.strip().splitlines()

        symmetric_phase(g, raw, reflect, pair_rows, center, eligible, run)
        axes = odd_phase(d, f, g, reflect, pair_rows, eligible, run)
        even_phase(g, reflect, pair_rows, center, eligible, axes, run)


if __name__ == "__main__":
    verify()
