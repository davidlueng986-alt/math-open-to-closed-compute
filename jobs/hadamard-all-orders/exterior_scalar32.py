"""Replay exact physical five-column profiles with a closed scalar mod32 histogram."""

from collections import Counter
import json
from pathlib import Path

from exterior_fold_trade import omitted_residual
from exterior_mod16_invariant import decode, low_high_moments
from exterior_orientation import paired_counts
from exterior_reindexed_pivot import SECOND
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture


def check_lower(columns, lower, weights, reference, beta, upper_gram):
    half = BOTTOM // 2
    require(all(sum((col >> r & 1) == 0 for col in columns) == weight.bit_count() for r, weight in enumerate(weights)),
            'exact physical row weights')
    require(all(a.bit_count() == b.bit_count() and (a >> half).bit_count() == (b >> half).bit_count()
                for a, b in zip(columns, reference, strict=True)), 'exact column weights in both halves')
    gram = correlations(columns, columns, BOTTOM)
    require(all(upper_gram[i][j] + gram[i][j] == ORDER * (i == j) for i in range(WIDTH) for j in range(WIDTH)),
            'the exact new-column Gram')
    raw = correlations(lower, columns, BOTTOM)
    require([raw[i] for i in LOWER_OMISSIONS] == beta, 'all 35 exact omitted-column projections')
    return raw


def lower_signed(raw):
    return {i: tuple(-x for x in values) for i, values in enumerate(raw) if i not in LOWER_OMISSIONS}


def check_payload(payload, columns, lower, weights, reference, beta, upper_gram, upstairs, anchors):
    raw = check_lower(columns, lower, weights, reference, beta, upper_gram)
    signed = lower_signed(raw)
    counts = paired_counts(signed, upstairs, anchors)
    require(counts == payload['joint_matches'] and counts[0] == 1193, 'the named exact pairs extend to full joint mod8')
    require(low_high_moments(upstairs.values()) == low_high_moments(signed.values()), 'all exact mixed-bit moments')
    special = sum(tuple(v % 16 for v in row) == (6, 4, 12, 14, 14) for row in signed.values())
    require(special == payload['special'], 'exact special residue count')
    return raw, counts


def anchors_from_pairs(pairs):
    half = BOTTOM // 2
    anchors = {i: j for base, a, b in pairs for i, j in ((base, a), (base + half, b))}
    require(len(anchors) == len(set(anchors.values())) == 2 * len(pairs), 'distinct complete Sylvester pairs')
    require(not set(anchors) & set(LOWER_OMISSIONS), 'all named lower columns are retained')
    return anchors


def main():
    here = Path(__file__).parent
    data = json.loads((here / 'exterior_scalar32_witness.json').read_text())
    pivot = json.loads((here / 'exterior_reindexed_pivot_witness.json').read_text())['ten']
    above = decode(json.loads((here / 'exterior_mod16_invariant_witness.json').read_text())['upper'])
    top, lower, _, weights = gram_fixture()
    half = BOTTOM // 2
    reference = decode(pivot['lower'])
    upstairs = {i: tuple(v) for i, v in enumerate(correlations(top[3:], above, TOP), start=3)}
    upper_gram = correlations(above, above, TOP)
    initial_raw = correlations(lower, reference, BOTTOM)
    beta = [initial_raw[i] for i in LOWER_OMISSIONS]
    factors = json.loads((here / 'exterior_exact_factor_witnesses.json').read_text())
    require(beta[1:] == [[-2 * x for x in row] for row in factors[7]['factor']], 'original omitted factor eight')
    alpha = correlations(top[1:3], above, TOP)
    require(all(x == 0 for row in omitted_residual(alpha, beta, upper_gram) for x in row), 'exact omitted Gram')

    critical = [pair for pair in pivot['anchors'] if pair[0] in (12, 14, 18, 313)]
    anchors = anchors_from_pairs(critical)
    original = anchors_from_pairs(pivot['anchors'])
    require(len(anchors) == 8 and len(original) == 20, 'the original and critical exact named pairs')
    support = data['flip_pairs']
    require(len(support) == len(set(support)) == 16 and all(0 <= r < half for r in support), 'sixteen physical base orientations')
    copy = reference[SECOND] ^ (reference[SECOND] >> half)
    require(sum(copy >> r & 1 for r in support) == 8, 'eight flips in each fold class')
    switches = sum((1 << r) | (1 << (r + half)) for r in support)
    second = reference[SECOND] ^ switches

    transition = data['transition']
    require(len(transition['lower']) == BOTTOM and transition['axis'] in (0, 2, 3, 4), 'physical transition data')
    after = decode(transition['lower'])
    exchanged = transition['axis']
    require(after[SECOND] == second and ((after[SECOND] ^ after[exchanged]) & switches) == switches,
            'exactly the two opposite signs can exchange on all thirty-two rows')
    before = list(after)
    before[SECOND] ^= switches
    before[exchanged] ^= switches
    previous = check_lower(before, lower, weights, reference, beta, upper_gram)
    raw, counts = check_payload(transition, after, lower, weights, reference, beta, upper_gram, upstairs, anchors)
    require(paired_counts(lower_signed(previous), upstairs, anchors)[0] == 1193, 'before exchange all critical matches extend')
    require(all((x - y) % 8 == 0 for a, b in zip(previous, raw, strict=True) for x, y in zip(a, b, strict=True)),
            'the exchange preserves each indexed joint mod8 label')
    require(all((a[SECOND] - b[SECOND]) % 8 == 0 for a, b in zip(raw, initial_raw, strict=True)), 'each scalar indexed mod8 label')
    require({i for i, j in original.items() if -raw[i][SECOND] == upstairs[j][SECOND]}
            == set(anchors) | {387, 430, 1167}, 'four complete original scalar pairs and three extra original scalar projections')

    scalar_scores = []
    for modulus in (8, 16, 32, 64, None):
        key = int if modulus is None else lambda x: x % modulus
        ue = Counter(key(row[SECOND]) for row in upstairs.values())
        le = Counter(key(row[SECOND]) for row in lower_signed(raw).values())
        scalar_scores.append(sum((ue & le).values()))
    require(scalar_scores == [1193, 1193, 1193, 1161, 1142], 'full scalar mod32 and exact finer overlaps')
    print(f'n=2396 scalar mod32 transition: 4 complete named pairs, scalar {tuple(scalar_scores)}, joint {tuple(counts)}')

    growth = data['growth']
    require(len(growth['lower']) == BOTTOM, 'one sign mask per lower row')
    columns = decode(growth['lower'])
    require(columns[SECOND] == second, 'every repaired second-column sign is kept')
    wider = anchors_from_pairs(critical + growth['extra_anchors'])
    require(anchors.items() < wider.items(), 'all four original critical complete pairs remain fixed')
    _, counts = check_payload(growth, columns, lower, weights, reference, beta, upper_gram, upstairs, wider)
    print(f'n=2396 scalar mod32 growth: {len(wider) // 2} complete named pairs, same 1193 scalar mod32, joint {tuple(counts)}')


if __name__ == '__main__':
    main()
