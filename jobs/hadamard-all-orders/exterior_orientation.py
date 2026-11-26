"""Enumerate the exact second-column orientations of the ten-pair configuration."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from exterior_fold_trade import omitted_residual
from exterior_mod16_invariant import decode
from exterior_reindexed_pivot import SECOND
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture
from verify import paley


# The first price is for the weight equation, then the prices of the selected
# Paley columns in omitted-column order followed by their ten anchor indices.
PRICE = (
    ('-29/9', '0', '-14/9', '-10/9', '0', '16/9', '4/9', '-8/9', '2/3', '-2/9', '14/9', '4/3', '0'),
    ('5', '-1', '1/2', '0', '-5', '-1/2', '-2', '0', '0', '1/2', '-1/2', '-1/2', '0', '-1/2', '1/2'),
)


def support(rows, paley_columns, copy):
    half = BOTTOM // 2
    counts = Counter()
    eligible = []
    for r, (first, second) in enumerate(zip(rows[:half], rows[half:], strict=True)):
        if ((first ^ second) >> SECOND & 1) != copy or any(v.bit_count() in (0, WIDTH) for v in (first, second)):
            continue
        sign = 1 - 2 * (first >> SECOND & 1)
        if copy == 0:
            price = -sign * (paley_columns[1] >> r & 1)
        else:
            price = sign * (1 - (paley_columns[978 - half] >> r & 1) - (paley_columns[1013 - half] >> r & 1))
        counts[price] += 1
        if price == 0:
            eligible.append(r)
    require(counts == ({0: 66, 1: 137}, {0: 105, 1: 126})[copy], 'exact one-copy orientation support')
    return eligible


def enumerate_copy(executable, positions, rows, paley_columns, fixed, copy):
    half = BOTTOM // 2
    signs = tuple(1 - 2 * (rows[r] >> SECOND & 1) for r in positions)
    columns = [i % half for i in fixed if i // half == copy and i % half]
    equations = [signs] + [tuple((paley_columns[i] >> r & 1) * u for r, u in zip(positions, signs, strict=True))
                           for i in columns]
    prices = tuple(map(Fraction, PRICE[copy]))
    dual = [sum(price * a for price, a in zip(prices, coefficients, strict=True))
            for coefficients in zip(*equations, strict=True)]
    bound = sum(max(0, 1 - value) for value in dual)
    require(bound == (Fraction(128, 9), Fraction(15))[copy], 'exact rational orientation bound')
    # Equal counts of positive and negative flips make the total size even.
    limit = bound // 2
    require(limit == 7, 'maximum number of flips of either sign')

    redundant = [tuple(x - y for x, y in zip(a, b, strict=True)) for a, b in combinations(equations, 2)]
    encoded = {}
    for equation in equations + redundant:
        require(set(equation) <= {-1, 0, 1}, 'each coefficient is a signed unit or zero')
        positive = sum(1 << i for i, a in enumerate(equation) if a == 1)
        negative = sum(1 << i for i, a in enumerate(equation) if a == -1)
        if (negative, positive) not in encoded:
            encoded[positive, negative] = None

    def words(value):
        return value & ((1 << 64) - 1), value >> 64

    lines = [f'{len(positions)} {len(encoded)} {limit}']
    lines += [' '.join(map(str, words(pos) + words(neg))) for pos, neg in encoded]
    result = subprocess.run([executable], input='\n'.join(lines) + '\n', check=True, capture_output=True, text=True)
    masks = []
    for line in result.stdout.splitlines():
        lo, hi = map(int, line.split())
        local = lo | (hi << 64)
        require(local >> len(positions) == 0 and local.bit_count() <= 2 * limit, 'one-copy orientation mask')
        masks.append(sum(1 << r for i, r in enumerate(positions) if local >> i & 1))
    require(len(masks) == len(set(masks)) == (40, 2)[copy] and 0 in masks, 'exact distinct orientations per copy')
    return masks


def paired_counts(signed, upstairs, exact):
    require(len(exact) == len(set(exact.values())) and all(signed[i] == upstairs[j] for i, j in exact.items()),
            'every named pair matches exactly and is physically distinct')
    remaining_below = [v for i, v in signed.items() if i not in exact]
    used = set(exact.values())
    remaining_above = [v for i, v in upstairs.items() if i not in used]
    counts = []
    for modulus in (8, 16, 32, 64, None):
        key = tuple if modulus is None else lambda v: tuple(x % modulus for x in v)
        counts.append(len(exact) + sum((Counter(map(key, remaining_above)) & Counter(map(key, remaining_below))).values()))
    return counts


def check_refinement(fixture, previous, exact, upstairs, lower, weights, gram, beta):
    half = BOTTOM // 2
    require(len(fixture['lower']) == BOTTOM, 'complete refined placement')
    columns = decode(fixture['lower'])
    require(columns[SECOND] == previous[SECOND], 'all 1200 signs of the repaired scalar column')
    require(all(sum((col >> r & 1) == 0 for col in columns) == weight.bit_count() for r, weight in enumerate(weights)),
            'all exact physical row weights')
    require(all(a.bit_count() == b.bit_count() and (a >> half).bit_count() == (b >> half).bit_count()
                for a, b in zip(columns, previous, strict=True)), 'all exact half and global column weights')
    require(correlations(columns, columns, BOTTOM) == gram, 'exact new Gram is preserved')
    raw = correlations(lower, columns, BOTTOM)
    require([raw[i] for i in LOWER_OMISSIONS] == beta, 'exact omitted factor and omitted Gram are preserved')
    distinct = {p + half * s: (a, b)[s] for p, a, b in fixture['extra_anchors'] for s in (0, 1)}
    require(len(distinct) == 6 and not set(exact) & set(distinct), 'three additional complete Sylvester pairs')
    signed = {i: tuple(-v for v in value) for i, value in enumerate(raw) if i not in LOWER_OMISSIONS}
    counts = paired_counts(signed, upstairs, exact | distinct)
    require(counts == fixture['joint_matches'] and counts[0] == 1193 and len(exact | distinct) == 20,
            'full joint mod8 with ten prescribed exact pairs')
    special = sum(tuple(x % 16 for x in value) == (6, 4, 12, 14, 14) for value in signed.values())
    require(special == 2, 'exact special mod16 multiplicity')
    print(f'n=2396 released anchor refinement: 10 complete pairs, same 1193 scalar mod16; joint matches {tuple(counts)}')


def check_release(here, fixture, above, top, lower, weights):
    witness = json.loads((here / 'exterior_orientation_witness.json').read_text())
    half = BOTTOM // 2
    released = witness['released']
    exchanged = witness['exchange_column']
    support = witness['base_rows']
    require(released == 384 and exchanged in (0, 2, 3, 4) and support == [1, 151, 303, 356, 569, 578],
            'release and six changed base orientations')
    name_to_pair = {p: (i, j) for p, i, j in fixture['anchors']}
    exact = {p + half * s: name_to_pair[p][s] for p in witness['complete_anchors'] for s in (0, 1)}
    require({12, 14, 18, 313} <= set(witness['complete_anchors']) <= set(name_to_pair) - {released}
            and len(exact) == 2 * len(witness['complete_anchors']) == len(set(exact.values())),
            'claimed complete anchors are distinct and keep both critical pivots')

    row_mask = sum(1 << r for r in support)
    switched = row_mask | row_mask << half
    require(len(witness['lower']) == BOTTOM, 'complete physical lower placement')
    after = decode(witness['lower'])
    before = list(after)
    require((after[exchanged] ^ after[SECOND]) & switched == switched, 'exchanged signs must be opposite')
    before[exchanged] ^= switched
    before[SECOND] ^= switched
    original = decode(fixture['lower'])
    require(before[SECOND] == original[SECOND], 'exactly twelve second signs moved by the exchange')
    require(all(sum((col >> r & 1) == 0 for col in after) == weight.bit_count() for r, weight in enumerate(weights)),
            'all exact physical row weights')
    require(all(a.bit_count() == b.bit_count() and (a >> half).bit_count() == (b >> half).bit_count()
                for columns in (before, after) for a, b in zip(columns, original, strict=True)),
            'all exact half and global column weights')
    second_delta = after[SECOND] ^ original[SECOND]
    require(second_delta & ((1 << half) - 1) == second_delta >> half, 'fixed second fold')

    upper_dots = correlations(top[3:], above, TOP)
    old_gram = correlations(above, above, TOP)
    gram = correlations(after, after, BOTTOM)
    require(gram == correlations(before, before, BOTTOM), 'the physical exchange preserves the new Gram')
    require(all(old_gram[i][j] + gram[i][j] == ORDER * (i == j) for i in range(WIDTH) for j in range(WIDTH)),
            'all exact new-column orthogonalities')
    raw = correlations(lower, after, BOTTOM)
    pre = correlations(lower, before, BOTTOM)
    initial = correlations(lower, original, BOTTOM)
    beta = [raw[i] for i in LOWER_OMISSIONS]
    factors = json.loads((here / 'exterior_exact_factor_witnesses.json').read_text())
    require(beta == [pre[i] for i in LOWER_OMISSIONS] == [initial[i] for i in LOWER_OMISSIONS]
            and beta[1:] == [[-2 * x for x in row] for row in factors[7]['factor']], 'all exact factor-eight projections')
    alpha = correlations(top[1:3], above, TOP)
    require(all(x == 0 for row in omitted_residual(alpha, beta, old_gram) for x in row), 'all exact omitted Gram entries')
    require(all((x - y) % 8 == 0 for a, b in zip(raw, pre, strict=True) for x, y in zip(a, b, strict=True)),
            'the exchange keeps all indexed mod8 vectors')
    require(all((a[SECOND] - b[SECOND]) % 8 == 0 for a, b in zip(raw, initial, strict=True)), 'the scalar labels stay fixed')

    signed = {i: tuple(-v for v in value) for i, value in enumerate(raw) if i not in LOWER_OMISSIONS}
    upstairs = {i: tuple(value) for i, value in enumerate(upper_dots, start=3)}
    require(all(signed[i] == upstairs[j] and tuple(-v for v in pre[i]) == upstairs[j] for i, j in exact.items()),
            'both stages preserve every claimed complete pair')
    scalar_anchors = {p + half * s: pair[s] for p, pair in name_to_pair.items() if p != released for s in (0, 1)}
    require(all(signed[i][SECOND] == upstairs[j][SECOND] for i, j in scalar_anchors.items())
            and tuple(signed[i][SECOND] for i in (released, released + half)) == (8, -16)
            and tuple(-initial[i][SECOND] for i in (released, released + half)) == (0, -16),
            'nine complete scalar pairs, only one anchor value released')
    require(Counter(v[SECOND] % 16 for v in signed.values()) == Counter(v[SECOND] % 16 for v in upstairs.values()),
            'full scalar mod16 histogram simultaneously with the exact Gram matrices')

    counts = paired_counts(signed, upstairs, exact)
    require(counts == witness['joint_matches'] and counts[0] == 1193, 'complete joint mod8 with fixed exact anchors')
    print(f'n=2396 released anchor {released}: {len(exact) // 2} complete pairs, 9 scalar pairs, 1193 scalar mod16; '
          f'joint matches {tuple(counts)}')
    check_refinement(witness['refinement'], after, exact, upstairs, lower, weights, gram, beta)


def main():
    here = Path(__file__).parent.resolve()
    fixture = json.loads((here / 'exterior_reindexed_pivot_witness.json').read_text())['ten']
    above = decode(json.loads((here / 'exterior_mod16_invariant_witness.json').read_text())['upper'])
    top, lower, _, weights = gram_fixture()
    half = BOTTOM // 2
    paley_columns = paley(half - 1)
    rows = [int(v, 32) for v in fixture['lower']]
    require([v.bit_count() for v in rows] == [v.bit_count() for v in weights], 'exact reference row weights')
    reference = decode(fixture['lower'])[SECOND]
    fixed = (*LOWER_OMISSIONS, *(i for p, _, _ in fixture['anchors'] for i in (p, p + half)))
    require(len(fixed) == len(set(fixed)) == 27, 'seven omitted and twenty named scalar projections')
    baseline = [-v[0] for v in correlations(lower, [reference], BOTTOM)]
    upstairs = [v[SECOND] for v in correlations(top[3:], above, TOP)]
    require(all(baseline[i] == upstairs[j - 3] for p, a, b in fixture['anchors']
                for i, j in ((p, a), (p + half, b))), 'exact scalar anchor values')

    with TemporaryDirectory() as directory:
        executable = Path(directory) / 'orientation'
        subprocess.run(['g++', '-O3', '-std=c++20', '-Wall', '-Wextra', '-Werror',
                        here / 'exterior_orientation.cpp', '-o', executable], check=True)
        copies = [enumerate_copy(executable, support(rows, paley_columns, f), rows, paley_columns, fixed, f)
                  for f in (0, 1)]

    retained = tuple(i for i in range(BOTTOM) if i not in LOWER_OMISSIONS)
    moduli = (8, 16, 32, 64, None)
    keys = tuple(int if m is None else lambda x, m=m: x % m for m in moduli)
    targets = [Counter(map(key, upstairs)) for key in keys]
    require(set(targets[1]) == {0, 4, 8, 12} and (targets[1][8], targets[1][12]) == (312, 292),
            'exact modulo-sixteen scalar target')
    caps = [0] * len(moduli)
    optimal = []
    for left, right in product(*copies):
        require(not left & right, 'one orientation belongs to exactly one copy')
        change = left | right
        second = reference ^ (change | change << half)
        require(second.bit_count() == reference.bit_count() and (second >> half).bit_count() == (reference >> half).bit_count(),
                'both exact half weights')
        signed = [-v[0] for v in correlations(lower, [second], BOTTOM)]
        require(all(signed[i] == baseline[i] for i in fixed), 'all fixed scalar projections')
        require(all((a - b) % 8 == 0 for a, b in zip(signed, baseline, strict=True)), 'all indexed scalar mod8 labels')
        value = [signed[i] for i in retained]
        counts = [sum((target & Counter(map(key, value))).values()) for target, key in zip(targets, keys, strict=True)]
        caps = [max(a, b) for a, b in zip(caps, counts, strict=True)]
        if counts[1] == 1189:
            optimal.append((change.bit_count(), tuple(counts), tuple(sorted(Counter(v % 16 for v in value).items()))))

    require(caps == [1193, 1189, 1169, 1140, 1127], 'exact separate scalar maxima over all eighty orientations')
    require(len(optimal) == 6 and len({histogram for _, _, histogram in optimal}) == 5, 'six optimizers and five histograms')
    require(any(flips == 12 and counts == (1193, 1189, 1150, 1140, 1126) for flips, counts, _ in optimal),
            'twelve-pair scalar witness for the mod16 bound')
    print(f'n=2396 anchored fixed second fold: 40 x 2 orientations, scalar match caps {tuple(caps)}')
    check_release(here, fixture, above, top, lower, weights)


if __name__ == '__main__':
    main()
