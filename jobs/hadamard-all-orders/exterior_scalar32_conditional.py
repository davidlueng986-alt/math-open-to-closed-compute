"""Check simultaneous mixed congruences and why two successful folds cannot both stay."""

from collections import Counter
from itertools import product
import json
from pathlib import Path

from exterior_fold_trade import omitted_residual
from exterior_mod16_invariant import decode
from exterior_scalar32 import anchors_from_pairs, check_payload, lower_signed
from exterior_scalar32_fold_rank import ALL, HALF, RESIDUES, conditional_labels, deficit
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, TOP, correlations, require
from five_column_gram import gram_fixture


def target_and_overlap(upper, lower, key):
    return sum((Counter(map(key, upper)) & Counter(map(key, lower))).values())


def check_two_marginals(above, below):
    counts = tuple(target_and_overlap(above, below.values(), lambda row: (row[1] % 16, row[j] % 8))
                   for j in (0, 2, 3, 4))
    require(counts == (1189, 1193, 1185, 1193), 'the third and fifth mixed marginals both close')

    cohorts = tuple(tuple(sum(1 << (i % HALF) for i, row in below.items() if i // HALF == side and row[1] % 16 == t)
                          for t in RESIDUES) for side in (0, 1))
    labels = conditional_labels((0, 3), above, below, cohorts)
    caps = tuple(1193 - deficit(labels, cohorts, first, second) for first, second in product((0, ALL), repeat=2))
    require(caps == (1185, 1153, 1170, 1138), 'equal changes of the other two folds cannot close the joint condition')
    print(f'n=2396 scalar32 simultaneous marginals: {counts}; preserving both matched folds caps joint mod16 at {max(caps)}')


def main():
    here = Path(__file__).parent
    stored = json.loads((here / 'exterior_scalar32_conditional_witness.json').read_text())
    require(set(stored) == {'marginals', 'mixed'}, 'both distinct physical witnesses are present')
    baseline = json.loads((here / 'exterior_scalar32_witness.json').read_text())['growth']
    pivot = json.loads((here / 'exterior_reindexed_pivot_witness.json').read_text())['ten']
    upper = decode(json.loads((here / 'exterior_mod16_invariant_witness.json').read_text())['upper'])
    top, lower, _, weights = gram_fixture()
    reference = decode(baseline['lower'])
    top_dots = correlations(top[3:], upper, TOP)
    above = dict(enumerate(map(tuple, top_dots), start=3))
    upper_gram = correlations(upper, upper, TOP)
    baseline_raw = correlations(lower, reference, BOTTOM)
    beta = [baseline_raw[i] for i in LOWER_OMISSIONS]
    alpha = correlations(top[1:3], upper, TOP)
    factors = json.loads((here / 'exterior_exact_factor_witnesses.json').read_text())
    require(beta[1:] == [[-2 * v for v in row] for row in factors[7]['factor']]
            and all(x == 0 for row in omitted_residual(alpha, beta, upper_gram) for x in row), 'factor eight and exact omitted Gram')
    anchors = anchors_from_pairs([pair for pair in pivot['anchors'] if pair[0] in (12, 14, 18, 313)])
    require(len(anchors) == 8, 'four critical complete Sylvester pairs')
    require(target_and_overlap(top_dots, lower_signed(baseline_raw).values(), lambda row: row[1] % 32) == 1193,
            'the pinned physical second column closes its scalar mod32 histogram')

    for name, witness in stored.items():
        require(len(witness['lower']) == BOTTOM, 'one stored sign mask per physical row')
        columns = decode(witness['lower'])
        require(columns[1] == reference[1], 'identical all second-column signs')
        raw, _ = check_payload(witness, columns, lower, weights, reference, beta, upper_gram, above, anchors)
        signed = lower_signed(raw)
        observed = tuple(target_and_overlap(top_dots, signed.values(),
                         lambda row: (row[1] % modulus, *(row[j] % 8 for j in (0, 2, 3, 4))))
                         for modulus in (8, 16, 32))
        require(observed == tuple(witness['mixed_matches']), 'joint mixed-modulus signature matches')
        if name == 'marginals':
            check_two_marginals(top_dots, signed)
        else:
            require(name == 'mixed' and observed == (1193, 1177, 1085), 'the independent stronger mixed histogram')
            print(f'n=2396 scalar32 joint mixed histogram: {observed} at second mod 8, 16 and 32 with all other mod8')


if __name__ == '__main__':
    main()
