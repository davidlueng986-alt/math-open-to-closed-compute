"""Verify the E1920 four-channel pairing with exact modulo-sixteen auxiliary numerator."""

from collections import Counter, defaultdict
from hashlib import sha256
import json
from itertools import product
from pathlib import Path

from stack_1197_four_channels import LOWER_OMITTED, sources
from stack_1198_auxiliary import frames, multiply
from stack_1198_channels import signatures
from stack_1198_four_channels import SHARP_CAP_LOWER, SHARP_CAP_UPPER, check_channel_support, sorted_pairing
from stack_1198_joint import dot
from verify import verify_orthogonal


def main():
    upper, lower, u, v = sources()
    n, m = len(upper), len(lower)
    x = upper[411] ^ sum(1 << i for i in SHARP_CAP_UPPER)
    y = lower[30] ^ sum(1 << i for i in SHARP_CAP_LOWER)
    assert dot(n, u, x) == dot(m, v, y) == 0
    assert tuple(dot(m, y, lower[j]) // 2 for j in LOWER_OMITTED) == (-18, 4, 34, -30)
    # The omitted source columns all have negative first projections in this source.
    assert all(dot(m, v, lower[j]) < 0 for j in LOWER_OMITTED)
    beta = tuple(-dot(m, y, lower[j]) for j in LOWER_OMITTED)
    r = tuple(tuple(1 - 2 * (i == j) for j in range(4)) for i in range(4))
    candidates = [tuple(tuple(value // 2 for value in row) for row in multiply(e, r)) for e, _, _ in frames()[0]]
    assert any(tuple(sum(a*b for a, b in zip(row, f, strict=True)) for row in k) == beta
               for k in candidates for f in product((-1, 1), repeat=4)
               if sum(a*b for a, b in zip(r[0], f, strict=True)) == 0)

    a, deck_a = signatures(upper, u, x)
    b, deck_b = signatures(lower, v, y)
    assigned = {j: deck_a[i][1] for i, j in sorted_pairing(deck_a, deck_b).items()}
    path = Path(__file__).with_name('stack_1198_four_channel_mod16_data.json')
    updates = {int(j): value for j, value in json.loads(path.read_text(encoding='ascii')).items()}
    assert len(updates) == 156 and updates.keys() <= assigned.keys()
    assert all(assigned[j] != value for j, value in updates.items())
    assigned.update(updates)
    supply = defaultdict(list)
    for i, sig in enumerate(deck_a):
        supply[sig].append(i)
    residues = [0] * m
    columns = [None] * n
    universe = (1 << m) - 1
    for j, desired in sorted(assigned.items()):
        i = supply[deck_b[j][0], desired].pop()
        a1, a2 = a[i]
        b1, b2 = b[j]
        sign = -1 if (a1 or a2) * (b1 or b2 or 1) > 0 else 1
        assert a1 + sign * b1 == 0
        residues[j] = sign*a2 + b2
        lower_column = lower[j] if sign > 0 else lower[j] ^ universe
        columns[i] = upper[i] | lower_column << n
    assert all(not available for available in supply.values())
    columns.append(u | v << n)
    assert verify_orthogonal(n + m, columns) == 715806
    second = x | y << n
    assert Counter(abs(dot(n+m, col, second)) for col in columns) == {0: 1077, 4: 120}
    assert Counter(map(abs, residues)) == {0: 1080, 4: 120}
    channel_data = check_channel_support(residues, (3, 5))
    assert channel_data == ((26, 34, 34, 26), (416, 544, 544, 416), (147, 140, 146, 142))
    nonzero = [(value // 4, lower[j]) for j, value in enumerate(residues) if value]
    assert all(sum(value * (2 * (col >> i & 1) - 1) for value, col in nonzero) % 4 == 0 for i in range(m))
    digest = sha256(''.join(f'{word:x}\n' for word in [*columns, second]).encode('ascii')).hexdigest()
    assert digest == '27af0a94b12256edb4ae1fa79e3ee6bff306d63928fa9c04b0c009dc2f780ae0'
    print('Four-channel E1920 re-pairing: all auxiliary numerator rows pass modulo 16; odd modulus remains')
    print('Four-channel E1920: energy (416, 544, 544, 416), rank bases modulo 3 and 5; packed SHA256', digest)


if __name__ == '__main__':
    main()
