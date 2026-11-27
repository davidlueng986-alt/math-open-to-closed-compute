from fractions import Fraction
from itertools import combinations
import json
from math import prod
from random import Random

import numpy as np


PRIMES = (2, 3, 5, 7, 11)
DEPTHS = (4, 2, 1, 1, 1)
PRIME_POWERS = dict(zip(PRIMES, (p**depth for p, depth in zip(PRIMES, DEPTHS))))
PERIOD = prod(PRIME_POWERS.values())
POINTS = np.arange(PERIOD, dtype=np.int64)


def count_by_coordinate(mask, p):
    power = PRIME_POWERS[p]
    return mask.reshape(-1, power).sum(axis=0)


def finite_replay(rules, eta, threshold):
    v_mask = np.ones(PERIOD, dtype=bool)
    cylinders = {}
    for n, a, pair in rules:
        cylinders[n, a] = POINTS % n == a
        v_mask &= ~cylinders[n, a]

    unions = {}
    residual = []
    promoted = 0
    for n, a, pair in rules:
        projections = tuple((p, np.gcd(n, PRIME_POWERS[p])) for p in pair)
        for p, power in projections:
            cell = POINTS % power == a % power
            if int((v_mask & cell).sum()) * eta.denominator <= (PERIOD // power) * eta.numerator:
                assert n % power == 0
                positive_points = POINTS + 1
                activated = positive_points[(positive_points >= n) & (positive_points % n == a)]
                assert np.all((activated - a) % power == 0)
                assert np.all(activated >= power)
                promoted += 1
                break
        else:
            residual.append((n, a, pair))
            unions.setdefault(pair, np.zeros(PERIOD, dtype=bool))
            unions[pair] |= cylinders[n, a]

    good = {}
    for p, power in PRIME_POWERS.items():
        load = sum((count_by_coordinate(mask, p) for pair, mask in unions.items() if p in pair),
                   np.zeros(power, dtype=np.int64))
        good[p] = load <= threshold * (PERIOD // power)
        v_by_coordinate = count_by_coordinate(v_mask, p)
        assert np.all(2 * eta.denominator * v_by_coordinate[~good[p]] <= eta.numerator * (PERIOD // power))

    c = eta**2 / 4
    all_groups = np.zeros(PERIOD, dtype=np.int64)
    trimmed = {}
    b = max((sum(m == n for m, _, _ in rules) for n, _, _ in rules), default=1)
    for pair, mask in unions.items():
        p, q = pair
        keep = good[p][POINTS % PRIME_POWERS[p]] & good[q][POINTS % PRIME_POWERS[q]]
        trimmed[pair] = keep & mask
        untrimmed_count = np.zeros(PERIOD, dtype=np.int64)
        weights = 0
        for n, a, which_pair in residual:
            if which_pair != pair:
                continue
            cylinder = cylinders[n, a]
            assert int((cylinder & keep).sum()) * c.denominator >= (PERIOD // n) * c.numerator
            untrimmed_count += cylinder
            weights += PERIOD // n
        assert int(np.dot(untrimmed_count, untrimmed_count)) <= 36 * b * weights
        assert int(trimmed[pair].sum()) * 36 * b * c.denominator**2 >= c.numerator**2 * weights
        all_groups += trimmed[pair]

    for p, power in PRIME_POWERS.items():
        load = sum((count_by_coordinate(mask, p) for pair, mask in trimmed.items() if p in pair),
                   np.zeros(power, dtype=np.int64))
        assert np.all(load <= threshold * (PERIOD // power))

    total = int(all_groups.sum())
    variance_numerator = PERIOD * int(np.dot(all_groups, all_groups)) - total**2
    assert not np.any(all_groups[v_mask])
    assert variance_numerator <= (1 + 2 * threshold) * PERIOD * total
    assert total * int(v_mask.sum()) <= (1 + 2 * threshold) * PERIOD**2
    return len(residual), promoted, len(trimmed)


def main():
    rng = Random(250227)
    moduli = [((p**e) * (q**f), (p, q))
              for p, q in combinations(PRIMES, 2)
              for e in range(1, DEPTHS[PRIMES.index(p)] + 1)
              for f in range(1, DEPTHS[PRIMES.index(q)] + 1)]

    totals = [0, 0, 0]
    for index in range(240):
        multiplicity = index % 4 + 1
        rules = []
        anchor = rng.randrange(PERIOD)
        for n, pair in rng.sample(moduli, rng.randrange(7, len(moduli) + 1)):
            if index % 2 == 0:
                choices = range(n)
            else:
                choices = range(anchor % pair[0], n, pair[0])
            rules.extend((n, a, pair)
                         for a in rng.sample(choices, rng.randrange(1, min(multiplicity, len(choices)) + 1)))
        for eta, threshold in ((Fraction(1, 20), 4), (Fraction(1, 5), 3), (Fraction(1, 2), 2)):
            for i, value in enumerate(finite_replay(rules, eta, threshold)):
                totals[i] += value
    print(json.dumps(dict(cases=720, residual_rules=totals[0], promotions=totals[1], support_groups=totals[2])))


if __name__ == '__main__':
    main()

