"""Replay exact structured support exclusions for the second exterior fold."""

from collections import Counter
import json
from pathlib import Path
import subprocess
import sys

from exterior_mod16_invariant import decode
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, WIDTH, correlations, require
from five_column_gram import gram_fixture
from verify import paley, rows_from_columns


PRIME = 599
LENGTH = PRIME + 1
SECOND = 1
CUTS = (
    (0, {978: 1, 1013: 1}),
    (2, {1: 1}),
    (0, {1013: 1, 1108: 1}),
    (0, {602: 1, 978: 1, 1013: 1, 1108: 1}),
)
EXPECTED_SPECTRA = {13: {80: 46, 104: 230, 132: 1196}, 23: {116: 26}}
EXPECTED_SCREEN = {
    (13, 80): ((14328080, 22030, 0), (2204320, 6680, 0)),
    (13, 104): ((68333920, 7076, 0), (14328080, 3212, 0)),
    (13, 132): ((335277072, 1018, 0), (94565328, 724, 0)),
    (23, 116): ((7537816, 198, 0), (1806584, 88, 0)),
}


def binary_run(executable, mode, rows):
    data = "\n".join(" ".join(map(str, row)) for row in rows) + "\n"
    result = subprocess.run([executable, mode], input=data, capture_output=True, check=True, text=True)
    return result.stdout.splitlines()


def reduce(word, pivots):
    while word:
        place = word.bit_length() - 1
        if place not in pivots:
            break
        word ^= pivots[place]
    return word


def dependencies(vectors):
    pivots = {}
    kernel = []
    for word, combination in vectors:
        while word:
            place = word.bit_length() - 1
            if place not in pivots:
                pivots[place] = word, combination
                break
            old, source = pivots[place]
            word ^= old
            combination ^= source
        else:
            kernel.append(combination)
    return pivots, kernel


def check_code(columns, squares):
    pivots = {}
    for column in columns:
        word = reduce(column, pivots)
        if word:
            pivots[word.bit_length() - 1] = word
    require(len(pivots) == 300 and all(column.bit_count() % 4 == 0 for column in columns),
            "dimension and doubly-even generators")
    require(all((a & b).bit_count() % 2 == 0 for a in columns for b in columns), "self-dual column code")
    generator = next(a for a in sorted(squares) if len({pow(a, k, PRIME) for k in range(len(squares))}) == len(squares))
    translation = [0] + [1 + (x + 1) % PRIME for x in range(PRIME)]
    inversion = [1, 0] + [1 + pow(-x, -1, PRIME) for x in range(1, PRIME)]
    dilation = [0] + [1 + generator * x % PRIME for x in range(PRIME)]
    for transform in (translation, inversion, dilation):
        require(all(reduce(sum((column >> r & 1) << t for r, t in enumerate(transform)), pivots) == 0
                    for column in columns), "the physical Paley column code is invariant under projective generators")


def scalar_capacities(lower, archive):
    reference = archive["lower"]
    rows = [int(s, 32) for s in reference]
    projected = correlations(lower, decode(reference), BOTTOM)
    require([projected[i] for i in LOWER_OMISSIONS[1:]]
            == [[-2 * value for value in row] for row in archive["factor"]], "physical reference realizes factor eight")
    weights = [row.bit_count() for row in rows]
    bit_options = [(0,) if weight == 0 else (1,) if weight == WIDTH else (0, 1) for weight in weights]
    global_weight = sum(row >> SECOND & 1 for row in rows)
    capacities = []
    for weight_price, omitted_prices in CUTS:
        wanted = weight_price * global_weight + sum(price * projected[index][SECOND]
                                                    for index, price in omitted_prices.items())
        pointwise = [[], []]
        for r in range(LENGTH):
            fold = (rows[r] ^ rows[r + LENGTH]) >> SECOND & 1
            first = sum(price * (2 * (lower[index] >> r & 1) - 1) for index, price in omitted_prices.items())
            second = sum(price * (2 * (lower[index] >> (r + LENGTH) & 1) - 1)
                         for index, price in omitted_prices.items())
            for changed in (0, 1):
                values = [weight_price * (x + y) + first * (1 - 2 * x) + second * (1 - 2 * y)
                          for x in bit_options[r] for y in bit_options[r + LENGTH] if x ^ y ^ fold == changed]
                pointwise[changed].append(max(values))
        slack = sum(pointwise[0]) - wanted
        delta = [after - before for before, after in zip(*pointwise, strict=True)]
        capacities.append((slack, delta))
    expected = ((16, {-4: 229, 0: 300, 4: 71}), (0, {-4: 197, 0: 300, 4: 103}),
                (88, {-4: 215, 0: 300, 4: 85}), (16, {-8: 74, -4: 172, 0: 225, 4: 128, 8: 1}))
    require(tuple((slack, dict(Counter(delta))) for slack, delta in capacities) == expected,
            "all four exact local coefficient censuses")
    return capacities


def periodic_words(executable, period, cap, squares, columns, row_signatures):
    dilation = next(a for a in sorted(squares) if a != 1 and pow(a, period, PRIME) == 1)
    projective = [0] + [1 + dilation * x % PRIME for x in range(PRIME)]
    unseen = set(range(LENGTH))
    orbits = []
    while unseen:
        start = r = min(unseen)
        orbit = []
        while r in unseen:
            unseen.remove(r)
            orbit.append(r)
            r = projective[r]
        require(r == start, "dilation orbits")
        orbits.append(orbit)
    require(Counter(map(len, orbits)) == {1: 2, period: (PRIME - 1) // period}, "projective cycle lengths")
    vectors = []
    for i, orbit in enumerate(orbits):
        word = 0
        for r in orbit:
            word ^= row_signatures[r]
        vectors.append((word, 1 << i))
    _, basis = dependencies(vectors)
    require(len(basis) == (24 if period == 13 else 14), "dimension of the periodic subcode")
    singletons = sum(1 << i for i, orbit in enumerate(orbits) if len(orbit) == 1)
    mask = (1 << len(orbits)) - 1
    lines = binary_run(executable, "census", [(len(basis), period, cap, singletons, mask), basis])
    marker, *counts = lines[-1].split()
    spectrum = {w: int(counts[w]) for w in range(1, cap + 1) if int(counts[w])}
    require(marker == "spectrum" and len(counts) == LENGTH + 1 and sum(map(int, counts)) == (1 << len(basis)) - 1,
            "complete Gray-code census")
    require(spectrum == {k: n for k, n in EXPECTED_SPECTRA[period].items() if k <= cap}, "low-weight census")
    solutions = []
    for line in lines[:-1]:
        weight, orbit_word = map(int, line.split())
        word = sum(1 << r for i, orbit in enumerate(orbits) if orbit_word >> i & 1 for r in orbit)
        require(word.bit_count() == weight and all((word & column).bit_count() % 2 == 0 for column in columns),
                "each listed support has the prescribed weight and lies in the physical code")
        solutions.append((weight, word))
    require(Counter(w for w, _ in solutions) == spectrum and len(set(solutions)) == len(solutions),
            "all low-weight supports")
    return dilation, solutions


def screen(executable, period, weight, dilation, words, squares, capacities):
    subgroup = {pow(dilation, i, PRIME) for i in range(period)}
    require(len(subgroup) == period, "dilation order")

    def representatives(group):
        remaining = set(group)
        while remaining:
            a = min(remaining)
            yield a
            remaining.difference_update(a * d % PRIME for d in subgroup)

    remaining = {word for w, word in words if w == weight}
    shapes = []
    while remaining:
        word = min(remaining)
        infinity = word & 1
        points = [x for x in range(PRIME) if word >> (x + 1) & 1]
        remaining.difference_update(infinity + sum(1 << (1 + a * x % PRIME) for x in points) for a in squares)
        shapes.append(points + ([PRIME] if infinity else []))
    affine = list(representatives(squares))
    nonaffine = list(representatives(set(range(1, PRIME)) - squares))
    rows = [(len(shapes),)]
    rows.extend((len(shape), *shape) for shape in shapes)
    rows.extend(((len(affine), *affine), (len(nonaffine), *nonaffine)))
    rows.extend((slack // 4, *(v // 4 for v in delta)) for slack, delta in capacities[:2])
    counts = tuple(tuple(map(int, row.split())) for row in binary_run(executable, "period", rows))
    require(counts == EXPECTED_SCREEN[period, weight], "all projective settings fail at least one of two integer cuts")
    total = sum(count for count, _, _ in counts)
    print(f"n=2396 periodic second-fold exclusion: period {period}, weight {weight}, {total} parameter settings")
    return total


def check_shortening(executable, row_signatures, capacities):
    scores = [a + b for a, b in zip(capacities[0][1], capacities[1][1], strict=True)]
    require(Counter(scores) == {-4: 280, 0: 292, 4: 28}, "combined local price regions")
    good = [r for r, score in enumerate(scores) if score >= 0]
    bad = [r for r, score in enumerate(scores) if score < 0]
    pivots, shortened = dependencies((row_signatures[r], 1 << r) for r in good)
    require(len(pivots) == 300 and len(shortened) == 20, "shortening rank and dimension")
    cosets = [0]
    for r in bad:
        word = row_signatures[r]
        representative = 1 << r
        while word:
            generator, source = pivots[word.bit_length() - 1]
            word ^= generator
            representative ^= source
        cosets.append(representative)

    def packed(word):
        return tuple(word >> (64 * i) & ((1 << 64) - 1) for i in range(10))

    rows = [(len(shortened), len(cosets), len(capacities)), *(packed(v) for v in shortened + cosets)]
    for slack, delta in capacities:
        nonzero = sorted(set(delta) - {0})
        rows.append((slack, len(nonzero)))
        for price in nonzero:
            rows.append((price, *packed(sum(1 << r for r, score in enumerate(delta) if score == price))))
    require(binary_run(executable, "shortening", rows) == ["0 0"], "all words with at most one negative-region position fail")
    print("n=2396 second-fold shortening: 281 cosets of dimension 20; zero viable nonzero words at radius one")


def main(executable, mode="all"):
    directory = Path(__file__).parent
    archive = json.loads((directory / "exterior_exact_factor_witnesses.json").read_text())[-1]
    _, lower, _, _ = gram_fixture()
    columns = paley(PRIME)
    row_signatures = rows_from_columns(LENGTH, columns)
    squares = {a * a % PRIME for a in range(1, PRIME)}
    check_code(columns, squares)
    capacities = scalar_capacities(lower, archive)
    targets = ((13, 80),) if mode == "quick" else EXPECTED_SCREEN
    cases = {}
    for period, weight in targets:
        if period not in cases:
            cap = max(w for p, w in targets if p == period)
            cases[period] = periodic_words(executable, period, cap, squares, columns, row_signatures)
    total = sum(screen(executable, period, weight, *cases[period], squares, capacities) for period, weight in targets)
    if mode != "quick":
        require(total == 538381200, "all four projective screens")
        check_shortening(executable, row_signatures, capacities)
    print(f"n=2396: verified {total} structured second-fold parameter settings")


if __name__ == "__main__":
    binary = str(Path(sys.argv[1]).resolve())
    main(binary, *sys.argv[2:])
