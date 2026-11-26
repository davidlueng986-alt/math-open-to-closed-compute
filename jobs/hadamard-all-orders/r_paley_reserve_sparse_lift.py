"""Check the fixed-exterior sparse-lift bounds and the exhaustion of five-site pivot supports."""

from collections import Counter, defaultdict
from itertools import combinations, product
import json
from math import isqrt
from pathlib import Path

from r_paley_full92_contrast import AGREE, OPPOSITE
from r_paley_full92_skew import build_source, frame
from r_paley_full92_unrestricted import NEXT_PIVOTS, NEXT_ROOTS, NEXT_SELECTED
from r_paley_isotropic_code import half_projections
from r_paley_punctured_fibre import ALT_SELECTED


PRIME = 599
ORDER = 1196
NORM = PRIME * 596
AXIS_COUNT = 17


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def check_sparse_bounds(c_rows, pivots, contact_matchings, coefficient_bound):
    pivot_rows = [c_rows[g] for g in pivots]
    assert max(sum(abs(dot(row, other)) for other in pivot_rows) for row in pivot_rows) <= 88
    full = (1 << AXIS_COUNT) - 1
    patterns = Counter()
    for g, row in c_rows.items():
        if g not in pivots:
            mask = sum((x > 0) << i for i, x in enumerate(row))
            patterns[min(mask, mask ^ full)] += 1
    assert max(patterns.values()) == 2
    for mask in patterns:
        neighbors = [mask ^ (1 << i) for i in range(AXIS_COUNT)]
        assert sum(patterns[min(p, p ^ full)] for p in neighbors) <= 3

    # Losing fifteen positions removes at most fifteen disjoint contacts per axis.
    computed = sum(isqrt(NORM // (len(matching) - 15)) for matching in contact_matchings)
    assert computed == coefficient_bound
    left = PRIME * 564 - (299 * coefficient_bound + 596)
    assert left > 0 and left**2 > 4 * 299 * coefficient_bound * 596
    extra = NORM // (2 * PRIME - coefficient_bound)**2
    assert extra <= 13
    for h in range(1, extra + 1):
        nonpivot = 15 + h
        spectral = 88 + min(17 * nonpivot, 13 * nonpivot + 14)
        assert 4 * h * (PRIME - spectral) > 596
    assert 2 * (PRIME - 88 - min(17 * 15, 13 * 15 + 14)) > 596

    small_spectral = max(min(20 * p, 88) + min(17 * (12 - p), 13 * (12 - p) + 14)
                         for p in range(13))
    assert small_spectral == 198 and 3 * small_spectral < PRIME
    print(f"15-site sparse lift: coefficient bound {computed}, at most {extra} preliminary shifts")


def kernel(c_rows, support):
    matrix = [list(row) for row in zip(*(c_rows[j] for j in support), strict=True)]
    pivots = []
    for j in range(len(support)):
        rank = len(pivots)
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][j] % PRIME), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][j] % PRIME, -1, PRIME)
        matrix[rank] = [inverse * x % PRIME for x in matrix[rank]]
        for i, row in enumerate(matrix):
            if i != rank and row[j] % PRIME:
                scale = row[j]
                matrix[i] = [(x - scale * y) % PRIME
                             for x, y in zip(row, matrix[rank], strict=True)]
        pivots.append(j)
    basis = []
    for j in set(range(len(support))) - set(pivots):
        word = [0] * len(support)
        word[j] = 1
        for i, k in enumerate(pivots):
            word[k] = -matrix[i][j] % PRIME
        basis.append(word)
    return basis


def supports_with_pivots(c_rows, pivots):
    """The unpivoted signed profiles must include a disjoint triple and pair."""
    codes = {g: sum((x > 0) << i for i, x in enumerate(row)) for g, row in c_rows.items()}
    nonpivots = [(g, code) for g, code in codes.items() if g not in pivots]
    full = (1 << AXIS_COUNT) - 1
    found = set()
    for count in range(1, 6):
        for indices in combinations(range(AXIS_COUNT), count):
            removed = sum(1 << i for i in indices)
            mask = full ^ removed
            chosen = {pivots[i] for i in indices}
            groups = defaultdict(list)
            for g, code in nonpivots + [(g, codes[g]) for g in chosen]:
                p = code & mask
                groups[min(p, p ^ mask)].append(g)
            pairs, triples = [], []
            for group in groups.values():
                pairs.extend((pair, len(chosen.intersection(pair))) for pair in combinations(group, 2))
                triples.extend((triple, len(chosen.intersection(triple)))
                               for triple in combinations(group, 3))
            for triple, t in triples:
                if t < count - 2:
                    continue
                for pair, u in pairs:
                    if t + u == count and not set(triple).intersection(pair):
                        found.add(tuple(sorted(triple + pair)))
    return found


def replay():
    # If one side of a zero-sum triple uses the magnitude of the first pair,
    # the only isotropic pattern admits no position with a size-two contact.
    pattern = (1, 1, -1, 129, -130)
    assert sum(pattern) == 0 and dot(pattern, pattern) % PRIME == 0
    assert {a for a in range(PRIME) if (a*a + 7) % PRIME == 0} == {259, 340}
    assert all(sum(s * x * (1 + (i == j)) for i, (s, x) in enumerate(
        zip(signs, pattern, strict=True))) % PRIME
        for j in range(5) for signs in product((1, -1), repeat=5))

    contact_file = Path(__file__).with_name("r_paley_reserve_span_contacts.json")
    contact_data = json.loads(contact_file.read_text())
    source = build_source()
    frame_rows, frame_pivots = frame()
    fixed_rows = tuple(frame_rows[j] for j in AGREE + OPPOSITE)
    fixed_pivots = tuple(frame_pivots[j] for j in AGREE + OPPOSITE)
    cases = (
        (NEXT_SELECTED, NEXT_ROOTS, NEXT_PIVOTS, 1031, set()),
        (ALT_SELECTED, (972, 1013, 1066, 1051, 429), (1027, 645, 204, 324, 636),
         1033, {(204, 353, 362, 468, 1181), (204, 362, 851, 920, 1081)}),
    )
    for (mask, rows, extra_pivots, bound, expected), matchings in zip(cases, contact_data, strict=True):
        retained = tuple(g for g in range(ORDER) if not ((mask >> g) & 1))
        pivots = fixed_pivots + extra_pivots
        axis_columns = []
        for r, g in zip(fixed_rows + rows, pivots, strict=True):
            projections = half_projections(source, source[g] ^ (1 << r))
            axis_columns.append(tuple(projections[j] - PRIME * (j == g) for j in retained))
        c_rows = dict(zip(retained, zip(*axis_columns, strict=True), strict=True))
        check_sparse_bounds(c_rows, pivots, matchings, bound)

        supports = supports_with_pivots(c_rows, pivots)
        assert supports == expected
        for support in sorted(supports):
            a, b = kernel(c_rows, support)
            assert all(dot(a, c) % PRIME == dot(b, c) % PRIME == 0
                       for c in zip(*(c_rows[j] for j in support), strict=True))
            determinant = (dot(a, b)**2 - dot(a, a) * dot(b, b)) % PRIME
            assert determinant == PRIME - 19
            assert pow(determinant, (PRIME - 1) // 2, PRIME) == PRIME - 1
        print(f"Five-site pivot supports: {len(supports)}, all have anisotropic kernels")

    print("Any new physical word has reserve-code distance at least six")


if __name__ == "__main__":
    replay()
