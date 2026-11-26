"""Verify an exact symmetric channel with a dense anti-channel pivot."""
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198 import pack, signs
from stack_1198_channels import signatures
from stack_1198_energy import check_boundary
from stack_1198_joint import dot
from verify import verify_orthogonal


def reciprocal_channels(lower, reference, witness):
    side = len(lower) // 2
    mask = (1 << side) - 1
    halves = signs(reference & mask, side), signs(reference >> side, side)
    first_symmetric = [(top + bottom) // 2 for top, bottom in zip(*halves, strict=True)]
    pivot = signs(lower[witness['lower_pivot']] & mask, side)
    omitted = signs(lower[witness['sparse_omit']] & mask, side)
    holes, support = set(witness['dense_holes']), set(witness['sparse_support'])
    dense = [0 if i in holes else pivot[i] for i in range(side)]
    negative = witness.get('sparse_negative')
    sparse = [witness['sparse_sign'] * omitted[i] * (-1 if i == negative else 1)
              if i in support else 0 for i in range(side)]
    perm, orientation = [None] * side, [1] * side
    for active in (False, True):
        rows = [i for i, value in enumerate(first_symmetric) if bool(value) == active]
        selected, idle = [i for i in rows if sparse[i]], [i for i in rows if not sparse[i]]
        vacant, filled = [i for i in rows if not dense[i]], [i for i in rows if dense[i]]
        pairs = [*zip(selected, vacant, strict=True), *zip(idle, filled, strict=True)]
        for i, j in pairs:
            perm[i] = j
            if active:
                orientation[j] = first_symmetric[i] * first_symmetric[j]
    assert set(perm) == set(range(side))

    def action(word):
        result = [0] * side
        for i, j in enumerate(perm):
            result[j] = orientation[j] * word[i]
        return result

    assert action(first_symmetric) == first_symmetric
    sparse = action(sparse)
    upper_y = pack([a + b for a, b in zip(sparse, dense, strict=True)])
    lower_y = pack([a - b for a, b in zip(sparse, dense, strict=True)])
    transformed = []
    for column in lower[:side]:
        word = pack(action(signs(column & mask, side)))
        transformed.append(word | (word << side))
    return [*transformed, *lower[side:]], upper_y | (lower_y << side)


def reconstruct(witness):
    upper, base = source_matrices()
    n, m = len(upper), len(base)
    side = m // 2
    assert 0 < witness['upper_pivot'] < n
    assert side <= witness['lower_pivot'] < m and witness['lower_pivot'] not in LOWER_OMITTED
    assert witness['sparse_omit'] in LOWER_OMITTED and witness['sparse_omit'] < side
    assert witness['sparse_sign'] in (-1, 1)
    radius = len(witness['upper_flips'])
    assert radius in (32, 34)
    assert (witness.get('sparse_negative') in witness['sparse_support']) == (radius == 34)
    for name, count, bound in (('upper_flips', radius, n), ('dense_holes', radius + 2, side),
                               ('sparse_support', radius + 2, side)):
        entries = witness[name]
        assert len(entries) == len(set(entries)) == count and all(0 <= i < bound for i in entries)
    u, v = flipped_column(n, UPPER_FLIPS), flipped_column(m, LOWER_FLIPS)
    x = upper[witness['upper_pivot']] ^ sum(1 << i for i in witness['upper_flips'])
    lower, y = reciprocal_channels(base, v, witness)
    assert lower[side:] == base[side:]
    assert verify_orthogonal(m, lower) == 719400
    assert [dot(m, v, col) for col in base] == [dot(m, v, col) for col in lower]
    assert dot(n, u, x) == dot(m, v, y) == 0
    check_boundary(lower, v, y)
    omitted_signs = [1 if dot(m, v, lower[j]) > 0 else -1 for j in LOWER_OMITTED]
    z = tuple(dot(m, y, lower[j]) // 2 * sign for j, sign in zip(LOWER_OMITTED, omitted_signs, strict=True))
    assert z == (-34, 30, -18, 4)
    dots_a, deck_a = signatures(upper, u, x)
    dots_b, deck_b = signatures(lower, v, y)
    assert dots_a[0][1] == dots_b[0][1]
    assert dots_a[witness['upper_pivot']][1] == dots_b[witness['lower_pivot']][1] == n - 2 * radius
    stock = defaultdict(list)
    for i, key in enumerate(deck_a):
        stock[key].append(i)
    pairs = {}
    symmetric = [j for j in range(side) if j not in LOWER_OMITTED]
    assert len(symmetric) == 597
    for j in symmetric:
        pairs[stock[deck_b[j]].pop()] = j
    slots_a, slots_b = defaultdict(list), defaultdict(list)
    for (p, t), indices in stock.items():
        for i in indices:
            slots_a[p].append((t, i))
    for j in range(side, m):
        if j not in LOWER_OMITTED:
            p, t = deck_b[j]
            slots_b[p].append((t, j))
    assert slots_a.keys() == slots_b.keys()
    for p, entries in slots_a.items():
        for (_, i), (_, j) in zip(sorted(entries), sorted(slots_b[p]), strict=True):
            pairs[i] = j
    assert set(pairs) == set(range(n)) and set(pairs.values()) == set(range(m)) - set(LOWER_OMITTED)
    packed = []
    anti_residuals = [0] * side
    for i, col in enumerate(upper):
        j = pairs[i]
        a1, a2 = dots_a[i]
        b1, b2 = dots_b[j]
        sign = -1 if (a1 or a2) * (b1 or b2) > 0 else 1
        assert a1 + sign * b1 == 0
        assert (a2 + sign * b2) % 4 == 0
        if j < side:
            assert a2 + sign * b2 == 0
        else:
            anti_residuals[j - side] = (sign * a2 + b2) // 4
        attached = lower[j] if sign > 0 else lower[j] ^ ((1 << m) - 1)
        packed.append(col | (attached << n))
    packed.append(u | (v << n))
    new = x | (y << n)
    assert verify_orthogonal(n + m, packed) == 715806
    residuals = [dot(n + m, col, new) for col in packed]
    values = Counter(map(abs, residuals))
    energy = sum(d*d for d in residuals)
    digest = sha256(''.join(f'{item:x}\n' for item in [*packed, new]).encode('ascii')).hexdigest()
    transformed = [sum(coef * (2 * (col >> row & 1) - 1)
                       for col, coef in zip(lower[side:], anti_residuals, strict=True) if coef)
                   for row in range(side)]
    assert sum(value * value for value in transformed) == side * (energy // 16)
    assert any(value % 25 for value in transformed)
    return values, energy, digest


def main():
    path = Path(__file__).with_name('stack_1198_reciprocal_data.json')
    records = json.loads(path.read_text(encoding='ascii'))
    assert set(records) == {'radius32', 'radius34'}
    values, energy, digest = reconstruct(records['radius32'])
    assert values == {0: 1082, 4: 108, 8: 7} and energy == 2176
    assert digest == '7de262ee8b1d8beb59c9e1d74b89b2d1f38f8a678633ed2520fee5cded7e543c'
    print('reciprocal channel: 597 exact symmetric slots; 1082 zero, 108 magnitude 4, 7 magnitude 8; anti energy 2176')
    print('stacked exact symmetric packed SHA256', digest)
    values, energy, digest = reconstruct(records['radius34'])
    assert values == {0: 1082, 4: 114, 8: 1} and energy == 1888
    assert digest == 'c069aa8bf4111bed1459a2d2713119cf32a979b392b951d78908dde13b7aeab0'
    print('reciprocal radius 34: 597 exact symmetric slots; 1082 zero, 114 magnitude 4, 1 magnitude 8; anti energy 1888')
    print('stacked radius-34 packed SHA256', digest)


if __name__ == '__main__':
    main()
