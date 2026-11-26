"""Check all three-replacement moves at the four-channel E1920 witness."""

import argparse
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path
import subprocess

from stack_1197_four_channels import LOWER_OMITTED, sources
from stack_1198 import projection_targets
from stack_1198_four_channels import SHARP_CAP_LOWER, SHARP_CAP_UPPER
from stack_1198_joint import dot, signature
from stack_1198_replacements import bit_sign, mask, signed_sum
from verify import rows_from_columns


GROUPS = (*range(4, 37, 4), 1132)
UPPER_PIVOT, LOWER_PIVOT = 411, 30


def features(columns, first, pivot, omitted, reference, lower_half):
    size = len(columns)
    kept = set(range(size)) - {pivot, *omitted}
    negative_first = mask(j for j in kept if first[j] < 0)
    groups = [mask(j for j in kept if abs(first[j]) == value) for value in GROUPS]
    orient = 1 if lower_half else -1
    result = []
    for i, row in enumerate(rows_from_columns(size, columns)):
        pivot_sign = bit_sign(columns[pivot], i)
        weights = tuple(orient * pivot_sign * signed_sum(row, negative_first ^ group, group) for group in groups)
        mutual = pivot_sign * bit_sign(reference, i)
        extra = ((0, mutual, *(pivot_sign * bit_sign(columns[j], i) for j in omitted))
                 if lower_half else (mutual, 0, 0, 0, 0, 0))
        result.append((*weights, *extra))
    return result


def deck(columns, first, word, omitted):
    return Counter(signature(a, dot(len(columns), word, c))
                   for j, (a, c) in enumerate(zip(first, columns, strict=True)) if j not in omitted)


def group_sums(a, b):
    return tuple(sum(q * (b[p, q] - a[p, q]) for p, q in a.keys() | b.keys() if p == g) // 4 for g in GROUPS)


def ordered_energy(a, b):
    top, bottom = defaultdict(list), defaultdict(list)
    for (p, q), k in a.items():
        top[p].extend([q] * k)
    for (p, q), k in b.items():
        bottom[p].extend([q] * k)
    return sum((x-y)**2 for p in top for x, y in zip(sorted(top[p]), sorted(bottom[p]), strict=True))


def folded(vector):
    # The last seven coordinates have magnitude at most one for a single move.
    # At radius three no nonzero last-coordinate sum can be a multiple of seven.
    assert max(map(abs, vector[9:])) <= 1
    return tuple(7 * vector[i] + vector[i + 9] if i < 7 else vector[i] for i in range(9))


def solve(verifier):
    upper, lower, u, v = sources()
    n, m = len(upper), len(lower)
    first_a = [dot(n, u, c) for c in upper]
    first_b = [dot(m, v, c) for c in lower]
    assert first_a[UPPER_PIVOT] == first_b[LOWER_PIVOT]
    x = upper[UPPER_PIVOT] ^ mask(SHARP_CAP_UPPER)
    y = lower[LOWER_PIVOT] ^ mask(SHARP_CAP_LOWER)
    assert dot(n, x, u) == dot(m, y, v) == 0
    projection = tuple(dot(m, y, lower[j]) // 2 for j in LOWER_OMITTED)
    assert projection == (-18, 4, 34, -30)
    targets = projection_targets(upper, lower, v, LOWER_OMITTED)
    assert (projection, 0) in targets
    assert min(max((abs(a-b)+1)//2 for a, b in zip(projection, new, strict=True))
               for new, _ in targets if new != projection) == 11

    vectors = (features(upper, first_a, UPPER_PIVOT, (), u, False),
               features(lower, first_b, LOWER_PIVOT, LOWER_OMITTED, v, True))
    candidates = {}
    for side, (weights, selected) in enumerate(zip(vectors, (SHARP_CAP_UPPER, SHARP_CAP_LOWER), strict=True)):
        free = set(range(len(weights))) - set(selected)
        for i, j in product(selected, free):
            change = tuple((b-a)//2 for a, b in zip(weights[i], weights[j], strict=True))
            key = folded(change)
            assert key not in candidates
            candidates[key] = (side, i, j, change)
    assert len(candidates) == 76_892
    start_a = deck(upper, first_a, x, ())
    start_b = deck(lower, first_b, y, LOWER_OMITTED)
    assert ordered_energy(start_a, start_b) == 1920
    target = (*group_sums(start_a, start_b), 0, 0, 0, 0, 0, 0)
    assert target == (12,-9,0,-8,3,5,-1,0,0,0,0,0,0,0,0,0)
    keys = sorted(candidates)
    request = '\n'.join([' '.join(map(str, folded(target))), str(len(keys)),
                          *(' '.join(map(str, row)) for row in keys)]) + '\n'
    result = subprocess.run([verifier], input=request, text=True, capture_output=True, check=True)
    triples = [tuple(map(int, line.split())) for line in result.stdout.splitlines()]
    assert len(triples) == len({tuple(sorted(row)) for row in triples}) == 797
    physical, minimum = 0, float('inf')
    for row in triples:
        assert len(row) == 3 and all(0 <= j < len(keys) for j in row)
        moves = [candidates[keys[j]] for j in row]
        assert tuple(map(sum, zip(*(change for _, _, _, change in moves), strict=True))) == target
        if len({(side, k) for side, i, j, _ in moves for k in (i, j)}) != 6:
            continue
        physical += 1
        new_x = x ^ mask(k for side, i, j, _ in moves if side == 0 for k in (i, j))
        new_y = y ^ mask(k for side, i, j, _ in moves if side == 1 for k in (i, j))
        assert dot(n, new_x, u) == dot(m, new_y, v) == 0
        assert tuple(dot(m, new_y, lower[j]) // 2 for j in LOWER_OMITTED) == projection
        new_a = deck(upper, first_a, new_x, ())
        new_b = deck(lower, first_b, new_y, LOWER_OMITTED)
        assert not any(group_sums(new_a, new_b))
        minimum = min(minimum, ordered_energy(new_a, new_b))
    assert (physical, minimum) == (782, 2752)
    print('Four-channel E1920: 76892 distinct replacement signatures; 797 triples, 782 disjoint; exact excluded')
    print('Four-channel E1920: smallest exact-moment energy 2752; projection change needs at least 11 replacements')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('verifier', type=Path, help='compiled stack_1198_replacements.cpp')
    solve(parser.parse_args().verifier.resolve(strict=True))
