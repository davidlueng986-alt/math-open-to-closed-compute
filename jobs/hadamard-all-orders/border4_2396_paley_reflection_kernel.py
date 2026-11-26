"""Replay the physical Paley reflection kernels over F2."""

from collections import Counter
from math import gcd

from border4_2396_paley_negative_norm import (
    CYCLIC, J, N, PEAK64_MASKS, augmentation, circular, inverse,
    paley_words, reflect, required_norm, shift,
)


def reflection_blocks(axis):
    return tuple((1 << i) | (1 << ((axis - i) % N))
                 for i in range(N) if i <= (axis - i) % N)


def head_words(d, k):
    f = J ^ d ^ shift(d, k)
    prescribed = shift(inverse(f, CYCLIC), k) ^ f
    assert prescribed == shift(reflect(prescribed), k) and prescribed.bit_count() % 2 == 0
    u = sum(1 << i for i in range(N) if i < (k - i) % N and prescribed >> i & 1)
    assert u ^ shift(reflect(u), k) == prescribed
    return u, u ^ f


def head_columns(u, v, axis):
    base = required_norm(u, v)
    return tuple(required_norm(u ^ mask, v ^ mask) ^ base for mask in reflection_blocks(axis))


def tail_columns(w, axis):
    b = w ^ shift(reflect(w), axis)
    before = augmentation(circular(w, reflect(w)))
    columns = []
    for mask in reflection_blocks(axis):
        delta = augmentation(shift(circular(mask, mask ^ b), N - axis))
        changed = w ^ mask
        assert delta == before ^ augmentation(circular(changed, reflect(changed)))
        columns.append(delta)
    return tuple(columns)


def rank(columns):
    lead = {}
    for value in columns:
        while value:
            index = value.bit_length() - 1
            if index not in lead:
                lead[index] = value
                break
            value ^= lead[index]
    return len(lead)


def compression(mask, modulus):
    result = 0
    while mask:
        bit = mask & -mask
        mask ^= bit
        result ^= 1 << ((bit.bit_length() - 1) % modulus)
    return result


def verify_head_images():
    d = sum((value < 0) << i for i, value in enumerate(paley_words()[1]))
    types = Counter()
    for k in range(1, 150):
        if gcd(k, N) != 1:
            continue
        columns = head_columns(*head_words(d, k), k)
        proper = []
        primitive = []
        for col in columns:
            x, y = compression(col, 13), compression(col, 23)
            proper.append(x << 23 | y)
            lifted = sum(((x >> (i % 13) ^ y >> (i % 23)) & 1) << i for i in range(N))
            primitive.append(col ^ lifted)
        types[(rank(columns), rank(proper), rank(primitive))] += 1
    assert types == {(146, 17, 132): 116, (145, 17, 132): 16}
    print(f"Paley head norm ranks (full, proper, primitive): {dict(types)}")


def verify_joint_axes():
    u, v, w = PEAK64_MASKS
    assert required_norm(u, v) == augmentation(circular(w, reflect(w)))
    head = head_columns(u, v, 4)
    assert len(head) == 150
    sizes = Counter()
    for axis in range(N):
        tail = tail_columns(w, axis)
        assert len(tail) == 150 and 146 <= rank(tail) <= 149
        sizes[300 - rank(head + tail)] += 1
    assert sizes == {151: 299}
    print(f"Paley split 4 joint physical reflection kernel dimensions: {dict(sizes)}")


if __name__ == "__main__":
    verify_head_images()
    verify_joint_axes()
