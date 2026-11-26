"""Verify compatible conditional labels and exact Gram cuts on five physical folds."""

from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from exterior_mod16_invariant import decode
from exterior_scalar32 import anchors_from_pairs
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture
from verify import paley


OTHER = (0, 2, 3, 4)
PAIRS = tuple(combinations(range(WIDTH), 2))
PRICES = (
    (1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1),
    (1, -1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1),
)


def row_prices(mask):
    bits = tuple(mask >> j & 1 for j in range(WIDTH))
    entry = tuple(bits[j] for j in OTHER) + tuple(bits[j] * bits[k] for j, k in PAIRS)
    return tuple(sum(p * v for p, v in zip(prices, entry, strict=True)) for prices in PRICES)


def check_fold(fixture, rows, old, upstairs, paley_columns, fixed):
    half = BOTTOM // 2
    folds = tuple(int(v, 32) for v in fixture['fold'])
    require(len(folds) == half, 'one candidate fold mask per physical base pair')
    before = tuple(rows[r] ^ rows[r + half] for r in range(half))
    changes = tuple(a ^ b for a, b in zip(before, folds, strict=True))
    require(all(not (v & 2) for v in changes), 'fixed physical second-column fold')
    words = [sum((v >> j & 1) << r for r, v in enumerate(changes)) for j in range(WIDTH)]
    require(all(v.bit_count() % 2 == 0 for v in words), 'even physical fold differences')
    q = [tuple((v & p).bit_count() % 2 for v in words) for p in paley_columns]
    require(all(not any(q[i % half]) for i in fixed), 'all omitted and named low labels stay pinned')
    projected = [tuple(x + 4 * v for x, v in zip(old[i], q[i % half], strict=True))
                 for i in range(BOTTOM) if i not in LOWER_OMISSIONS]
    require(Counter(tuple(v % 8 for v in row) for row in upstairs)
            == Counter(tuple(v % 8 for v in row) for row in projected), 'complete indexed joint mod8 in the equal-half-weight relaxation')
    axes = tuple(j - 1 for j in fixture['mixed_axes'])
    require(len(axes) == len(set(axes)) == 2 and set(axes) <= set(OTHER), 'two selected non-second axes')
    def key(row):
        return (row[1] % 16, *(row[j] % 8 for j in axes))
    require(Counter(map(key, upstairs)) == Counter(map(key, projected)), 'both selected axes jointly match against second mod16')
    return folds, sum(bool(v) for v in changes)


def main():
    here = Path(__file__).parent
    data = json.loads((here / 'exterior_scalar32_fold_capacity_witness.json').read_text())
    baseline = json.loads((here / 'exterior_scalar32_conditional_witness.json').read_text())['marginals']
    pivot = json.loads((here / 'exterior_reindexed_pivot_witness.json').read_text())['ten']
    upper = decode(json.loads((here / 'exterior_mod16_invariant_witness.json').read_text())['upper'])
    top, lower, _, weights = gram_fixture()
    rows = tuple(int(v, 32) for v in baseline['lower'])
    reference = decode(baseline['lower'])
    require(all(v.bit_count() == w.bit_count() for v, w in zip(rows, weights, strict=True)), 'exact reference row weights')
    top_gram = correlations(upper, upper, TOP)
    bottom_gram = correlations(reference, reference, BOTTOM)
    require(all(top_gram[j][k] + bottom_gram[j][k] == ORDER * (j == k) for j in range(WIDTH) for k in range(WIDTH))
            and all(a.bit_count() + b.bit_count() == ORDER // 2 for a, b in zip(upper, reference, strict=True)),
            'reference global column weights and exact new-column Gram')
    anchors = anchors_from_pairs([pair for pair in pivot['anchors'] if pair[0] in (12, 14, 18, 313)])
    upstairs = correlations(top[3:], upper, TOP)
    old = [tuple(-v for v in row) for row in correlations(lower, reference, BOTTOM)]
    require(len(anchors) == 8 and all(old[i] == tuple(upstairs[j - 3]) for i, j in anchors.items()), 'all four reference anchor pairs')
    paley_columns = paley(BOTTOM // 2 - 1)
    fixed = (*LOWER_OMISSIONS, *anchors)
    row_costs = tuple(row_prices(v) for v in range(1 << WIDTH))
    demand = tuple(sum(row_costs[v][j] for v in rows) for j in range(len(PRICES)))
    require(demand == (3918, 3896), 'the two exact integer demands')
    possible = [tuple(v for v in range(1 << WIDTH) if v.bit_count() == w.bit_count() and v & 2 == w & 2) for w in rows]
    half = BOTTOM // 2
    gaps = []
    changes = []
    for witness in data:
        folds, changed = check_fold(witness, rows, old, upstairs, paley_columns, fixed)
        price = witness['price']
        capacity = 0
        for r, f in enumerate(folds):
            compatible = [row_costs[v][price] + row_costs[v ^ f][price] for v in possible[r] if v ^ f in possible[r + half]]
            require(bool(compatible), 'both physical rows can realize the proposed fold with their exact weight and second sign')
            capacity += max(compatible)
        gap = demand[price] - capacity
        require(gap == witness['shortfall'] > 0, 'integer capacity contradiction for the fixed fold')
        gaps.append(gap)
        changes.append(changed)
    require(gaps == [52, 48, 52, 54, 30] and changes == [501, 497, 503, 516, 498],
            'five distinct checked row-compatible fold obstructions')
    print(f'n=2396 scalar32 conditional fold capacity: five locally realizable profiles, exact Gram shortfalls {tuple(gaps)}')


if __name__ == '__main__':
    main()
