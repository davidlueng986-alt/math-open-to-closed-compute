"""Rebuild the exact outer design and compatible inner columns."""

from hashlib import sha256
from itertools import combinations
from math import isqrt

from verify import goethals_seidel, length_299_words, rows_from_columns, verify_orthogonal


NINE_FLIPS = (
    (643, 893), (824, 814), (837, 980), (863, 748), (876, 1065),
    (987, 987), (1000, 1048), (1158, 1052), (1174, 1154),
)


def build(t, source, flips, w_columns=None, gamma_index=None):
    # This integer replay uses the prime-field quadratic character.
    assert t >= 3 and t % 2 == 1 and all(t % d for d in range(3, isqrt(t)+1, 2))
    height = 2 * t - 2
    order = 4 * t
    assert len(source) == height
    base_mask = (1 << height) - 1
    top_mask = (1 << t) - 1
    record_mask = (1 << order) - 1
    if w_columns is None:
        w_columns = range(t)
    w_columns = tuple(w_columns)
    if gamma_index is None:
        gamma_index = t
    used_columns = set(w_columns)
    assert len(used_columns) == len(w_columns) == t and gamma_index not in used_columns
    assert all(0 <= i < height for i in used_columns | {gamma_index})
    gamma = source[gamma_index]
    normalized = tuple(base_mask ^ gamma ^ col for col in source)
    words = [normalized[i] for i in w_columns]
    top_border = 1 << (order - 2)
    inner_border = 3 << (order - 2)
    squares = {i * i % t for i in range(1, t)}

    left, right = [], []
    for j, word in enumerate(words):
        core = sum(1 << i for i in range(t) if (j - i) % t in squares)
        positive_diagonal = core | (1 << j)
        left.append(positive_diagonal | (core << t) | (word << (2 * t)) | top_border)
        right.append(core | (positive_diagonal << t) | ((word ^ base_mask) << (2 * t)) | top_border)
    outside = left + right

    # The first two inner columns are constant and the row-chunk indicator.
    inside = [record_mask, (base_mask << (2 * t)) | inner_border]
    for row, g in flips:
        assert 0 <= g < height and g not in used_columns and g != gamma_index
        bottom = normalized[g]
        assert 0 <= row < height and bottom >> row & 1
        # A flip at a positive sign gives total row sum minus two on the bottom.
        bottom ^= 1 << row
        first = sum((col >> row & 1) << j for j, col in enumerate(words))
        second = first ^ top_mask
        inside.append(first | (second << t) | (bottom << (2 * t)) | inner_border)
    return outside, inside


def verify():
    t = 599
    order = 4 * t
    short = goethals_seidel(length_299_words())
    assert verify_orthogonal(2 * t - 2, short) == 714610
    outside, inside = build(t, short, ((0, 600),))
    columns = outside + inside
    assert len(outside) == 1198 and len(columns) == 1201
    assert verify_orthogonal(order, columns) == 720600

    point_mask = (1 << (order - 2)) - 1
    incidence = [col & point_mask for col in outside]
    block_masks = rows_from_columns(order - 2, incidence)
    assert len(set(block_masks)) == order - 2
    assert all(block.bit_count() == t for block in block_masks)
    assert all(col.bit_count() == 2 * t - 1 for col in incidence)
    assert all((a & b).bit_count() == t - 1 for a, b in combinations(incidence, 2))

    digest = sha256(b"".join(col.to_bytes((order + 7) // 8, "little") for col in columns)).hexdigest()
    assert digest == "74a0d9a6dd10e07c4c1b10055e45315437e6c5649f53b1ba9017ca75f3148cc6"
    print("R(599): 2-(1198,599,598) with 2394 distinct blocks, both inner design steps verified")
    print(f"Hadamard 2396 × 1201: 720600 zero pair products, packed column digest {digest}")

    same_outside, extended_inside = build(t, short, NINE_FLIPS)
    assert same_outside == outside and extended_inside[:2] == inside[:2]
    extended = same_outside + extended_inside
    assert len(extended) == 1209 and verify_orthogonal(order, extended) == 730236
    extended_digest = sha256(b"".join(col.to_bytes((order + 7) // 8, "little")
                                      for col in extended)).hexdigest()
    assert extended_digest == "326cbbeb6a9c591c9be8d55a5228aaf2fc8a9374bb7610a7130a68963a79d9a6"
    print(f"Hadamard 2396 × 1209 on the same outer design: 730236 zero pair products, digest {extended_digest}")

    # Normalizing lower rows does not change distances between columns, but
    # it determines which pairs of normalized rows are close on unused columns.
    height = 2 * t - 2
    mask = (1 << height) - 1
    unused = [mask ^ short[t] ^ col for col in short[t + 1:]]
    assert len(unused) == 596
    unused_rows = rows_from_columns(height, unused)
    distances = [(a ^ b).bit_count() for a, b in combinations(unused_rows, 2)]
    assert len(distances) == 714610 and min(distances) == 210
    assert 2 * t + 2 + len(unused) == 1796
    print("Fixed lower source: minimum unused-row distance 210; one-flip extension width at most 1796")


if __name__ == "__main__":
    verify()
