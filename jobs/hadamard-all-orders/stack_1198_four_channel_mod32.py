"""Rebuild the four-channel E4352 modulo-32 pairing and verify odd check targets."""

from collections import Counter, defaultdict
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from stack_1197_four_channels import LOWER_OMITTED, sources
from stack_1198_auxiliary import frames, multiply
from stack_1198_channels import signatures
from stack_1198_four_channel_compressed import SYLVESTER, dot as inner
from stack_1198_four_channels import (
    SHARP_CAP_LOWER, SHARP_CAP_UPPER, common_basis, conference_graph_columns, sorted_pairing,
)
from stack_1198_joint import dot
from verify import verify_orthogonal


def rebuild():
    path = Path(__file__).with_name('stack_1198_four_channel_mod32_data.json')
    data = json.loads(path.read_text(encoding='ascii'))
    upper, lower, u, v = sources()
    n, m = len(upper), len(lower)
    move = set(data['upper_move'])
    assert len(move) == 2 and len(move.intersection(SHARP_CAP_UPPER)) == 1 and not data['lower_move']
    x = upper[411] ^ sum(1 << i for i in (set(SHARP_CAP_UPPER) ^ move))
    y = lower[30] ^ sum(1 << i for i in SHARP_CAP_LOWER)
    assert dot(n, u, x) == dot(m, v, y) == 0

    top, top_deck = signatures(upper, u, x)
    bottom, bottom_deck = signatures(lower, v, y)
    omitted = tuple(bottom[j] for j in LOWER_OMITTED)
    assert omitted == ((-8, -36), (-36, 8), (-60, 68), (-68, -60))
    beta = tuple(-q for p, q in omitted)
    r = tuple(tuple(1 - 2 * (i == j) for j in range(4)) for i in range(4))
    for e, _, _ in frames()[0]:
        k = tuple(tuple(value // 2 for value in row) for row in multiply(e, r))
        if any(tuple(inner(row, f) for row in k) == beta and inner(r[0], f) == 0
               for f in product((-1, 1), repeat=4)):
            break
    else:
        raise AssertionError('no auxiliary boundary frame')

    desired = {j: top_deck[i][1] for i, j in sorted_pairing(top_deck, bottom_deck).items()}
    updates = {int(j): q for j, q in data['signed_second_updates'].items()}
    assert updates.keys() <= desired.keys() and all(desired[j] != q for j, q in updates.items())
    desired.update(updates)
    supply = defaultdict(list)
    for i, signature in enumerate(top_deck):
        supply[signature].append(i)

    old = [None] * n
    errors = [0] * m
    universe = (1 << m) - 1
    for j, q in sorted(desired.items()):
        p, b2 = bottom[j]
        i = supply[abs(p), q if p else abs(q)].pop()
        a1, a2 = top[i]
        needed = b2 - (q if p >= 0 else -q)
        sign = next(h for h in (-1, 1) if a1 + h * p == 0 and h * a2 + b2 == needed)
        errors[j] = needed
        old[i] = upper[i] | ((lower[j] if sign > 0 else lower[j] ^ universe) << n)
    assert all(not entries for entries in supply.values())
    old.append(u | (v << n))
    return old, x | (y << n), lower, errors


def check_odd_targets(errors):
    channels = [tuple(s // 4 for s in errors[c:c + 300]) for c in range(0, len(errors), 300)]
    sites = list(zip(*channels, strict=True))
    active = {j for j, site in enumerate(sites) if any(site)}
    assert len(active) == 63
    omissions = {j % 300 for j in LOWER_OMITTED}
    assert active & omissions == {214}
    graph = conference_graph_columns()
    support = common_basis(graph, active, omissions - active, (3, 5, 13))
    assert len(support) == 150
    assert sum(j not in LOWER_OMITTED and j % 300 not in support for j in range(1200)) == 597

    def failures(vector, modulus):
        return sum(sum(col[j] * x for col, x in zip(graph, vector, strict=True)) % modulus != 0
                   for j in range(150))

    modular_forms = ((-1, -1, 1, 0), (-1, 1, 0, 1), (1, 2, 3, 5))
    assert tuple(failures([inner(site, row) for site in sites], p)
                 for row, p in zip(modular_forms, (3, 3, 13), strict=True)) == (91, 94, 139)
    walsh = [tuple(inner(row, site) // 4 for row in SYLVESTER) for site in sites]
    assert all(all(inner(row, site) % 4 == 0 for row in SYLVESTER) for site in sites)
    assert Counter(sum(bool(t) for t in site) for site in walsh) == {0: 237, 1: 58, 2: 5}
    walsh_forms = ((1, 0, 1, 1), (0, 1, 1, -1))
    vectors = [[inner(site, row) for site in walsh] for row in walsh_forms]
    assert tuple(sum(x * x for x in row) for row in vectors) == (58, 56)
    assert tuple(failures(row, 25) for row in vectors) == (136, 127)

    local_states = [site for site in product(range(-2, 3), repeat=4)
                    if all(inner(row, site) % 4 == 0 for row in SYLVESTER)]
    assert len(local_states) == 49
    for site in local_states:
        transformed = tuple(inner(row, site) // 4 for row in SYLVESTER)
        assert max(map(abs, transformed)) <= 2 and sum(bool(t) for t in transformed) != 3
        assert (not any(site)) == all(inner(transformed, row) % 3 == 0 for row in walsh_forms)
        assert (not any(site)) == all(inner(site, row) % 3 == 0 for row in modular_forms[:2])
        assert (not any(site)) == (inner(site, modular_forms[-1]) % 13 == 0)
    print('Four-channel E4352 odd targets: 63 active base positions; 597 protected old slots')
    print('Two support-free Walsh checks modulo 25: squared norms (58, 56), failed equations (136, 127)')


def verify():
    old, second, lower, errors = rebuild()
    assert verify_orthogonal(2396, old) == 715806
    assert Counter(abs(dot(2396, c, second)) for c in old) == {0: 955, 4: 232, 8: 10}
    energies = tuple(sum(s * s for s in errors[c:c + 300]) for c in range(0, 1200, 300))
    assert energies == (1120, 1056, 1056, 1120) and sum(energies) == 4352
    nonzero = [(value // 4, lower[j]) for j, value in enumerate(errors) if value]
    assert all(sum(value * (2 * (col >> i & 1) - 1) for value, col in nonzero) % 8 == 0
               for i in range(1200))
    digest = sha256(''.join(f'{word:x}\n' for word in [*old, second]).encode('ascii')).hexdigest()
    assert digest == '4639a4d4d8e4dfc545ed88f6d51253e60f15d6eb6b228bea7f9bba8f99ec7a68'
    print('Four-channel E4352: full auxiliary numerator modulo 32; residual magnitude at most eight')
    print('Four-channel E4352 packed SHA256', digest)
    check_odd_targets(errors)


if __name__ == '__main__':
    verify()
