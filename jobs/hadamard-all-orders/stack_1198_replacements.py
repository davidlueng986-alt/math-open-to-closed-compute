"""Replay the exact three-replacement exclusion around the energy-2112 witness."""

import argparse
from collections import Counter, defaultdict
from itertools import product
import json
from pathlib import Path
import subprocess

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198 import projection_targets
from stack_1198_joint import dot, signature
from verify import rows_from_columns


def mask(positions):
    return sum(1 << i for i in positions)


def bit_sign(word, index):
    return 2 * (word >> index & 1) - 1


def signed_sum(left, right, positions):
    return positions.bit_count() - 2 * ((left ^ right) & positions).bit_count()


def row_moments(columns, size, kept, first, pivot, orientation):
    negative_first = mask(j for j in kept if first[j] < 0)
    groups = [mask(j for j in kept if abs(first[j]) == value) for value in range(4, 37, 4)]
    return [tuple(orientation * bit_sign(pivot, i) * signed_sum(row, negative_first ^ group, group)
                  for group in groups)
            for i, row in enumerate(rows_from_columns(size, columns))]


def enumerate_moment_triples(verifier, regions, selected):
    # Dividing the oriented projection gap by four makes each replacement shift integral.
    total = [sum(rows[i][j] for rows, support in zip(regions, selected, strict=True)
                 for i in support) // 2 for j in range(9)]
    target = tuple(-value for value in total)
    assert target == (4, -7, -11, 5, 3, -2, 4, -1, 0)
    moves = defaultdict(list)
    for region, (rows, support) in enumerate(zip(regions, selected, strict=True)):
        inactive = set(range(len(rows))) - set(support)
        for old, new in product(support, inactive):
            change = tuple((b - a) // 2 for a, b in zip(rows[old], rows[new], strict=True))
            moves[change].append((region, old, new))
    assert len(moves) == 75_733 and sum(map(len, moves.values())) == 75_736
    keys = sorted(moves)
    data = '\n'.join([' '.join(map(str, target)), str(len(keys)),
                      *(' '.join(map(str, key)) for key in keys)]) + '\n'
    result = subprocess.run([verifier], input=data, text=True, capture_output=True, check=True)
    triples = [tuple(map(int, row.split())) for row in result.stdout.splitlines()]
    assert len(triples) == len({tuple(sorted(triple)) for triple in triples}) == 3734
    physical = []
    for triple in triples:
        assert len(triple) == 3 and all(0 <= i < len(keys) for i in triple)
        vectors = tuple(keys[i] for i in triple)
        assert tuple(map(sum, zip(*vectors, strict=True))) == target
        physical.extend(product(*(moves[key] for key in vectors)))
    return physical


def verify(verifier):
    data = Path(__file__).with_name('stack_1198_channels_data.json')
    witness = json.loads(data.read_text(encoding='ascii'))
    upper, lower = source_matrices()
    n, m = len(upper), len(lower)
    side = m // 2
    half = (1 << side) - 1
    symmetric = [column & half for column in lower[:side]]
    antisymmetric = [column & half for column in lower[side:]]
    u = flipped_column(n, UPPER_FLIPS)
    v = flipped_column(m, LOWER_FLIPS)
    first_upper = [dot(n, u, column) for column in upper]
    first_lower = [dot(m, v, column) for column in lower]
    pivot_upper, pivot_lower = witness['upper_pivot'], witness['lower_pivot']
    omitted_anti, = (j - side for j in LOWER_OMITTED if j >= side)
    selected = [witness[key] for key in ('upper_flips', 'dense_holes', 'sparse_support')]
    assert list(map(len, selected)) == [32, 34, 34]
    assert first_upper[0] == first_lower[0] == 1132
    assert first_upper[pivot_upper] == first_lower[pivot_lower] == 0
    assert n - 2 * len(selected[0]) == m - 2 * len(selected[1]) == 1132
    keep_upper = set(range(n)) - {0, pivot_upper}
    keep_sym = set(range(side)) - {0, pivot_lower, *LOWER_OMITTED}
    keep_anti = set(range(side)) - {omitted_anti}
    source_x = upper[pivot_upper]
    source_h = symmetric[pivot_lower]
    source_w = antisymmetric[omitted_anti] ^ (half if witness['sparse_sign'] < 0 else 0)
    regions = [row_moments(upper, n, keep_upper, first_upper, source_x, -1),
               row_moments(symmetric, side, keep_sym, first_lower[:side], source_h, 1),
               row_moments(antisymmetric, side, keep_anti, first_lower[side:], source_w, -1)]
    triples = enumerate_moment_triples(verifier, regions, selected)
    assert len(triples) == 3734

    top_v = v & half
    different = top_v ^ (v >> side)
    same = half ^ different

    def lower_dots(holes, sparse):
        return [2 * signed_sum(source_h, column, half ^ holes) for column in symmetric] + [
            2 * signed_sum(source_w, column, sparse) for column in antisymmetric]

    baseline = lower_dots(mask(selected[1]), mask(selected[2]))
    projection = tuple(baseline[j] // 2 for j in LOWER_OMITTED)
    assert projection == (18, 4, 34, -30)
    targets = projection_targets(upper, lower, v)
    assert (projection, 0) in targets
    distances = [tuple((abs(a - b) + 1) // 2 for a, b in zip(projection, other, strict=True))
                 for other, _ in targets if other != projection]
    anti_index, = (i for i, j in enumerate(LOWER_OMITTED) if j >= side)
    assert min(dist[anti_index] + max(d for i, d in enumerate(dist) if i != anti_index)
               for dist in distances) == 18

    disjoint = physical = first_exact = 0
    for triple in triples:
        if len({(region, position) for region, old, new in triple for position in (old, new)}) != 6:
            continue
        disjoint += 1
        flip, holes, sparse = (mask(support) ^ mask(position for r, old, new in triple
                                                   if r == region for position in (old, new))
                               for region, support in enumerate(selected))
        if (holes & same).bit_count() != (sparse & same).bit_count():
            continue
        physical += 1
        x = source_x ^ flip
        lower_first_dot = 2 * (signed_sum(source_h, top_v, same & (half ^ holes))
                               + signed_sum(source_w, top_v, different & sparse))
        if dot(n, x, u) + lower_first_dot != 0:
            continue
        first_exact += 1
        top_deck = Counter(signature(a, dot(n, x, c)) for a, c in zip(first_upper, upper, strict=True))
        lower_deck = Counter(signature(a, b) for j, (a, b) in enumerate(
            zip(first_lower, lower_dots(holes, sparse), strict=True)) if j not in LOWER_OMITTED)
        assert top_deck != lower_deck
    assert (disjoint, physical, first_exact) == (3665, 3661, 3272)
    print('E2112: 75,736 replacements; exact exclusion through three with arbitrary old-column pairing')
    print('Three replacements: 3734 moment triples, 3665 disjoint, 3661 physical, 3272 first-exact, 0 full')
    print('Changing the oriented omitted direction requires at least 18 replacements in these supports')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('verifier', type=Path, help='compiled stack_1198_replacements.cpp')
    verify(parser.parse_args().verifier.resolve(strict=True))
