"""Verify the tensor Walsh residue theorem and the one-channel energy controls."""
from collections import Counter
from itertools import combinations, product
from math import gcd
from random import Random

from stack_odd_t_residual import conference_positive_columns, paley_type_two
from verify import verify_orthogonal


def walsh(k):
    size = 1 << k
    return tuple(tuple(1 - 2 * ((g & c).bit_count() % 2) for c in range(size))
                 for g in range(size))


def apply(matrix, vector):
    return tuple(sum(a * b for a, b in zip(row, vector, strict=True)) for row in matrix)


def rows_from_columns(columns):
    return tuple(tuple(2 * (word >> i & 1) - 1 for word in columns) for i in range(len(columns)))


def tensor_passes(base, frequencies, residual, modulus):
    transformed = tuple(apply(frequencies, local) for local in residual)
    return all(value % modulus == 0 for channel in zip(*transformed, strict=True)
               for value in apply(base, channel))


def full_mask(base, frequencies, residual):
    size = len(frequencies)
    half = size // 2
    output = tuple(apply(frequencies, local) for local in residual)
    if any(value % half for column in output for value in column):
        return None
    mask = tuple(value // half % 2 for value in output[0])
    if any(value // half % 2 != bit for column in output
           for value, bit in zip(column, mask, strict=True)):
        return None
    if any(sum((output[j][g] - half * bit * base[0][j]) // size
               for j in range(len(base))) % 2 for g, bit in enumerate(mask)):
        return None
    return mask


def energy(residual):
    return 16 * sum(value * value for local in residual for value in local)


def check_projection(residual, mask):
    slope = 0
    for g, work in enumerate(mask):
        if work:
            slope ^= g
    offset = tuple(local[0] % 2 for local in residual)
    assert sum(offset) % 2 == 0
    assert all((value - bit - (c & slope).bit_count()) % 2 == 0
               for local, bit in zip(residual, offset, strict=True)
               for c, value in enumerate(local))


def odd_bound(d, e):
    assert d % 2 == 1 and 1 < e <= d and d % e == 0
    return 2 * e * e // gcd(e * e, d)


def verify_mask_counts():
    size = 4
    frequencies = walsh(2)
    counts = Counter()
    for local in product(range(2 * size), repeat=size):
        w = apply(frequencies, local)
        if all(value % (size // 2) == 0 for value in w):
            counts[tuple(value // (size // 2) % 2 for value in w)] += 1
    assert len(counts) == 8 and set(counts.values()) == {256}
    for k in range(1, 4):
        frequencies = walsh(k)
        size = len(frequencies)
        masks = [b for b in product((0, 1), repeat=size) if not sum(b) % 2]
        for b in masks:
            local = tuple(value // 2 for value in apply(frequencies, b))
            assert apply(frequencies, local) == tuple(size // 2 * bit for bit in b)
        assert len(masks) == 2 ** (size - 1)
        if k >= 2:
            for offset, slope in product((0, 1), range(size)):
                local = [0] * size
                if slope:
                    local[0] = local[slope] = 1
                local[0] += 2 * (offset ^ (sum(local) // 2 % 2))
                assert all(value // 2 % 2 == (offset + (g & slope).bit_count()) % 2
                           for g, value in enumerate(apply(frequencies, local)))
            assert 2 ** (k + 1) == len({tuple((b + (g & h).bit_count()) % 2 for g in range(size))
                                        for b in (0, 1) for h in range(size)})
    nonlinear = (1, 1, 0, 0, 0, 0, 0, 0)
    assert sum(nonlinear) == 2
    assert all(nonlinear != tuple((b + (g & h).bit_count()) % 2 for g in range(8))
               for b in (0, 1) for h in range(8))


def verify_cap_one():
    for k in (1, 2, 3):
        frequencies = walsh(k)
        size = len(frequencies)
        half = size // 2
        category = Counter()
        for local in product((-1, 0, 1), repeat=size):
            w = apply(frequencies, local)
            if any(value % half for value in w):
                continue
            mask = tuple(g for g, value in enumerate(w) if value // half % 2)
            mass = sum(value * value for value in local)
            assert mass >= size * len(mask) // 4
            category[len(mask)] += 1
            if not mask:
                assert local == (0,) * size or any(
                    local == row or local == tuple(-value for value in row) for row in frequencies)
            elif len(mask) == 2:
                assert mass == half
            elif len(mask) == 4:
                a, b, c, d = mask
                assert a ^ b ^ c ^ d == 0
                assert sum(w[g] < 0 for g in mask) % 2 == 1
                assert mass == size
            else:
                raise AssertionError(mask)
        flats = size * (size - 1) * (size - 2) // 24
        assert category == {0: 1 + 2 * size, 2: 2 * size * (size - 1), **({4: 8 * flats} if flats else {})}


def verify_global_phases(base):
    rng = Random(69753)
    for k in (1, 2, 3):
        frequencies = walsh(k)
        size = len(frequencies)
        signs = base[0]
        for case in range(20):
            mask = tuple(1 if g in (0, case % (size - 1) + 1) else 0 for g in range(size))
            if case % 3 == 0:
                mask = (0,) * size
            shift = tuple(value // 2 for value in apply(frequencies, mask))
            phase = [[rng.randrange(-2, 3) for _ in range(size)] for _ in signs]
            for g in range(size):
                phase[-1][g] += sum(row[g] for row in phase) % 2
            residual = [tuple(a * b + z for b, z in zip(shift, apply(frequencies, u), strict=True))
                        for a, u in zip(signs, phase, strict=True)]
            assert full_mask(base, frequencies, residual) == mask
            assert tensor_passes(base, frequencies, residual, 2 * size)
            check_projection(residual, mask)
            assert energy(residual) >= 4 * size * len(base) * sum(mask)
            residual[0] = tuple(a + b for a, b in zip(residual[0], frequencies[case % size], strict=True))
            assert full_mask(base, frequencies, residual) is None
            assert not tensor_passes(base, frequencies, residual, 2 * size)


def verify_energy_controls(base):
    d = len(base) // 4
    frequencies = walsh(2)
    size = len(frequencies)
    sign_word = tuple((a + b) // 2 for a, b in zip(base[0], base[1], strict=True))
    assert sum(v * v for v in sign_word) == odd_bound(d, d) == 2 * d
    assert all(value % d == 0 for value in apply(base, sign_word))

    # The cap-one closure threshold is strict, and this residual reaches it.
    equal_channels = tuple((value,) * size for value in sign_word)
    assert energy(equal_channels) == 8 * size * len(base)
    assert full_mask(base, frequencies, equal_channels) == (0,) * size
    assert tensor_passes(base, frequencies, equal_channels, 2 * size)
    assert all(value % d == 0 for value in apply(base, sign_word))

    # A different cap-one residual attains the nonzero-mask energy threshold.
    half_support = (1, 0, 1, 0)
    assert apply(frequencies, half_support) == (2, 2, 0, 0)
    nonzero_mask = tuple(tuple(a * v for v in half_support) for a in base[0])
    assert full_mask(base, frequencies, nonzero_mask) == (1, 1, 0, 0)
    assert tensor_passes(base, frequencies, nonzero_mask, 2 * size)
    assert energy(nonzero_mask) == 8 * size * len(base)
    check_projection(nonzero_mask, (1, 1, 0, 0))

    # Short nonzero residuals can pass the 2-adic test. Check the required odd test directly.
    short = [frequencies[2], frequencies[2], *[(0,) * size for _ in range(len(base) - 2)]]
    assert tensor_passes(base, frequencies, short, 2 * size)
    assert energy(short) == 32 * size
    assert any(value % d for value in apply(base, tuple(local[0] for local in short)))


def verify_paley_mod25(base):
    conference = conference_positive_columns(149)
    side = len(conference)
    assert side == 150 and len(base) == 2 * side
    for i, j in product(range(side), repeat=2):
        c = 0 if i == j else 2 * (conference[j] >> i & 1) - 1
        assert (conference[j] >> i & 1) == (conference[i] >> j & 1)
        delta = int(i == j)
        assert base[i][j] == c + delta
        assert base[i + side][j] == base[i][j + side] == c - delta
        assert base[i + side][j + side] == -c - delta

    # PGL2 sends any three support points to infinity, zero and one.
    prefix_product = conference[0] ^ conference[1] ^ conference[2]
    without_prefix = ((1 << side) - 1) ^ 7
    total, maximum = 0, 0
    for i, j, k in combinations(range(3, side), 3):
        outside = without_prefix ^ (1 << i) ^ (1 << j) ^ (1 << k)
        parity = prefix_product ^ conference[i] ^ conference[j] ^ conference[k]
        imbalance = abs((side - 6) - 2 * (parity & outside).bit_count())
        maximum = max(maximum, imbalance)
        total += 1
    assert total == 518665 and maximum == 44 < 2 * (side - 12 - 24) - (side - 6)
    for count in (1, 3, 5):
        assert 9 * (side - 12) > 149 * count
    for count in (2, 4):
        assert 12 * count * count < 149 * count

    sharp = tuple((a + b) // 2 for a, b in zip(base[0], base[1], strict=True))
    assert sum(value * value for value in sharp) == 150
    assert all(value % 25 == 0 for value in apply(base, sharp))

def verify():
    base_columns = paley_type_two(5)
    assert len(base_columns) == 12 and verify_orthogonal(12, base_columns) == 66
    base = rows_from_columns(base_columns)
    # Reverse one source column so the first-row sign vector has odd negative parity.
    reversed_base = tuple(tuple(-v if j == 0 else v for j, v in enumerate(row)) for row in base)
    assert sum(base[0]) % 4 != sum(reversed_base[0]) % 4
    verify_mask_counts()
    verify_cap_one()
    verify_global_phases(base)
    verify_global_phases(reversed_base)
    verify_energy_controls(base)

    large = paley_type_two(149)
    assert len(large) == 300 and verify_orthogonal(300, large) == 44850
    assert odd_bound(75, 25) == 50 and 16 * 4 * odd_bound(75, 25) == 3200
    assert odd_bound(75, 75) == 150 and 16 * 4 * odd_bound(75, 75) == 9600
    large_base = rows_from_columns(large)
    verify_energy_controls(large_base)
    verify_paley_mod25(large_base)
    print('Odd-t Walsh tensor: full 2-adic masks, affine deck parity, cap-one energy controls')
    print('H4 tensor any H300: one modulo-25 channel suffices at cap 4 and total energy below 3200')
    print('Paley H300: modulo-25 channel gap 150 is sharp; cap 4 total energy threshold 9600')


if __name__ == '__main__':
    verify()
