"""Prove a sharp energy minimum for the two fixed E4352 words."""

import json
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path

from stack_1197_four_channels import LOWER_OMITTED
from stack_1198_channels import signatures
from stack_1198_four_channel_compressed import SYLVESTER, dot
from stack_1198_four_channel_mod32 import rebuild


def signed_demand(first, quotient):
    return abs(first), quotient if first > 0 else -quotient if first < 0 else abs(quotient)


def verify():
    path = Path(__file__).with_name('stack_1198_four_channel_energy_bound_data.json')
    proof = json.loads(path.read_text(encoding='ascii'))
    denominator = proof['denominator']
    assert denominator > 0

    old, next_column, lower, witness = rebuild()
    n, m = 1196, 1200
    upper_mask = (1 << n) - 1
    first = old[-1]
    upper = [column & upper_mask for column in old[:-1]]
    a, _ = signatures(upper, first & upper_mask, next_column & upper_mask)
    b, _ = signatures(lower, first >> n, next_column >> n)
    assert all(value % 4 == 0 for _, value in (*a, *b))
    supply = Counter(signed_demand(p, q // 4) for p, q in a)
    assert len(supply) == 112
    potentials = dict(zip(sorted(supply), proof['potentials'], strict=True))
    groups = defaultdict(list)
    for (p, q), value in potentials.items():
        groups[p].append((q, value))

    # A local quotient modulo four sets the scalar residue class of the
    # matching cost. The bound checks all integer signed signatures.
    prices = {}
    for i, (p, q) in enumerate(b):
        if i in LOWER_OMITTED:
            prices[i, 0] = 0
            continue
        for oriented, potential in groups[abs(p)]:
            required = (oriented,) if p > 0 else (-oriented,) if p < 0 else (oriented, -oriented)
            for value in required:
                residual = q // 4 - value
                position = i, residual % 4
                lower_price = denominator * residual**2 - potential
                if position not in prices or lower_price < prices[position]:
                    prices[position] = lower_price

    patterns = [r for r in product(range(4), repeat=4) if all(dot(r, h) % 4 == 0 for h in SYLVESTER)]
    assert len(patterns) == 16
    bases = []
    for j in range(300):
        configurations = [tuple((j + c*300, r[c]) for c in range(4)) for r in patterns]
        bases.append(min(sum(prices[position] for position in configuration)
                         for configuration in configurations if all(pos in prices for pos in configuration)))
    bound = sum(bases) + sum(count * potentials[key] for key, count in supply.items())
    assert bound == proof['bound'] == 2692917 and denominator == 10000
    # In the zero Walsh class the exact quotient squared norm is divisible by
    # eight. A nonzero class has residual energy at least 9600.
    assert 264 * denominator < bound <= 272 * denominator and 272 % 8 == 0
    assert sum(r * r for r in witness) == 16 * 272 == 4352
    print('Fixed four-channel words: unrestricted modulo-32 energy minimum 4352; integer dual 2692917/10000')


if __name__ == '__main__':
    verify()
