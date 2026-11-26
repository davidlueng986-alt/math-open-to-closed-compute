"""Check the four-channel upper rematch and lower energy bounds."""
from collections import defaultdict
from itertools import product

from stack_1197_four_channels import LOWER_OMITTED, sources
from stack_1198_four_channel_mod32 import rebuild
from stack_1198_four_channels import SHARP_CAP_LOWER, SHARP_CAP_UPPER
from stack_1198_joint import dot


SIDE = 300
BASE_MASK = (1 << SIDE) - 1
OMITTED = tuple(divmod(j, SIDE) for j in LOWER_OMITTED)
FREE = BASE_MASK ^ sum(1 << j for _, j in OMITTED)
KEPT = tuple(BASE_MASK ^ sum(1 << j for c, j in OMITTED if c == channel) for channel in range(4))


def old_upper_rows(upper, lower, packed, x):
    n, m = len(upper), len(lower)
    all_upper, all_lower = (1 << n) - 1, (1 << m) - 1
    label = {word: j for j, column in enumerate(lower) for word in (column, column ^ all_lower)}
    rows = [[0] * 4 for _ in upper]
    for old, col in zip(packed, upper, strict=True):
        assert old & all_upper == col
        channel, site = divmod(label[old >> n], SIDE)
        matching = all_upper ^ (col ^ x)
        while matching:
            bit = matching & -matching
            rows[bit.bit_length() - 1][channel] |= 1 << site
            matching ^= bit
    return rows


def phase_distance(parity, slope):
    q = [word ^ (BASE_MASK if (slope & c).bit_count() % 2 else 0)
         for c, word in enumerate(parity)]
    a, b, c, d = q
    odd = a ^ b ^ c ^ d
    two = ((a ^ b) & (c ^ d)) | (a & b & ~(c | d)) | (c & d & ~(a | b))
    majority = (a & b & (c | d)) | (c & d & (a | b))
    mismatch = (odd & FREE).bit_count() + 2 * (two & FREE).bit_count()
    offset_parity = (majority & FREE).bit_count() % 2
    for channel, site in OMITTED:
        offset = (channel & slope).bit_count() % 2
        ones = sum((word >> site) & 1 for word in q)
        mismatch += 4 - ones if offset else ones
        offset_parity ^= offset
    if offset_parity and not (two & FREE):
        mismatch += 2 if odd & FREE else 4
    return mismatch


def dynamic_distance(parity, slope):
    best = [0, 10**6]
    fixed = {j: (slope & c).bit_count() % 2 for c, j in OMITTED}
    for j in range(SIDE):
        after = [10**6, 10**6]
        for offset in ((fixed[j],) if j in fixed else (0, 1)):
            mismatch = sum(((word >> j) & 1) != (offset + (slope & c).bit_count()) % 2
                           for c, word in enumerate(parity))
            for previous in (0, 1):
                phase = previous ^ offset
                after[phase] = min(after[phase], best[previous] + mismatch)
        best = after
    return best[0]


def verify_upper(upper, lower, packed, reference, x):
    rows = old_upper_rows(upper, lower, packed, x)
    used = set(SHARP_CAP_UPPER) ^ {1154, 754}
    types = defaultdict(set)
    for i in range(len(upper)):
        types[((upper[411] ^ reference) >> i) & 1].add(i)
    minimum, witnesses, count = [10**6] * 4, [None] * 4, 0
    for group in types.values():
        for i, j in product(used & group, group - used):
            parity = tuple(mask & ~(a ^ b) for mask, a, b in zip(KEPT, rows[i], rows[j], strict=True))
            assert sum(word.bit_count() for word in parity) == 598
            for slope in range(4):
                cost = phase_distance(parity, slope)
                if cost < minimum[slope]:
                    minimum[slope] = cost
                    witnesses[slope] = parity
            count += 1
    assert count == 18626 and minimum == [332, 328, 328, 328]
    assert [dynamic_distance(parity, g) for g, parity in enumerate(witnesses)] == minimum


def sign(word, i):
    return 2 * ((word >> i) & 1) - 1


def verify_lower(lower, reference, y, r):
    m = len(lower)
    image = [sum(error * sign(column, i) for error, column in zip(r, lower, strict=True))
             for i in range(m)]
    weights = [m - sign(y, i) * value for i, value in enumerate(image)]
    energy = sum(error * error for error in r)
    assert energy == 4352 and sum(map(abs, r)) == 1008
    assert min(weights) == 1008
    assert energy + 4 * sum(sorted(weights)[:2]) == 12416

    types = defaultdict(set)
    pivot = lower[30]
    tests = [reference, *(lower[j] for j in LOWER_OMITTED)]
    for i in range(m):
        label = tuple(sign(pivot, i) * sign(column, i) for column in tests)
        types[label].add(i)
    flipped = set(SHARP_CAP_LOWER)
    moves = [(energy + 4 * (weights[i] + weights[j]), i, j)
             for group in types.values() for i, j in product(flipped & group, group - flipped)]
    assert len(moves) == 1109
    bound, i, j = min(moves)
    assert (bound, i, j) == (12672, 125, 1105)
    changed = y ^ (1 << i) ^ (1 << j)
    assert dot(m, changed, reference) == 0
    assert all(dot(m, changed, column) == dot(m, y, column) for column in tests)
    next_r = [value + dot(m, changed, column) - dot(m, y, column)
              for column, value in zip(lower, r, strict=True)]
    assert sum(value * value for value in next_r) == 12672 and max(map(abs, next_r)) == 12
    for i in range(m):
        new_image = sum(error * sign(column, i) for error, column in zip(next_r, lower, strict=True))
        assert m * sign(changed, i) - new_image == m * sign(y, i) - image[i]
        assert new_image % 32 == 0


def verify():
    upper, lower, u, v = sources()
    packed, candidate, used_lower, r = rebuild()
    assert used_lower == lower
    n = len(upper)
    verify_upper(upper, lower, packed[:-1], u, candidate & ((1 << n) - 1))
    verify_lower(lower, v, candidate >> n, r)
    print('Four-channel E4352 rigidity: 18626 upper moves need at least 328 old slot reassignments')
    print('Four-channel E4352 fixed pairing: every nonempty lower change has energy at least 12416')


if __name__ == '__main__':
    verify()
