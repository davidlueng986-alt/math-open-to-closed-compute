"""Verify 1197 exact columns and a jointly modulo-eight next column."""

from collections import defaultdict
from hashlib import sha256

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198 import pack, projection_targets, signs
from verify import verify_orthogonal


UPPER_PIVOT = 522
LOWER_PIVOT = 30
UPPER_SECOND_FLIPS = (
    459, 1001, 808, 266, 817, 572, 49, 80, 1155, 873, 97, 843, 714, 675, 327,
    382, 760, 585, 163, 965, 148, 74, 1164, 243, 1151, 165, 1051, 211, 794,
    1126, 342, 333,
)
LOWER_DENSE_HOLES = (
    298, 434, 439, 0, 271, 276, 97, 426, 299, 56, 499, 495, 542, 459, 126,
    279, 532, 127, 579, 22, 370, 165, 485, 261, 438, 10, 398, 76, 66, 341,
    590, 60, 32, 247,
)
LOWER_SPARSE_SUPPORT = (
    50, 240, 440, 87, 241, 383, 585, 328, 39, 32, 542, 450, 578, 438, 443,
    527, 419, 29, 209, 415, 113, 330, 177, 57, 238, 528, 176, 441, 370, 308,
    117, 148, 106, 212,
)
PACKED_HASH = "e7286d504cd73630268065c939e1140dfcaebe1bba165abc8c301ee5df3f9b6c"


def dot(size, left, right):
    return size - 2 * (left ^ right).bit_count()


def signature(first, second, modulus=None):
    oriented = second if first >= 0 else -second
    if modulus is not None:
        oriented %= modulus
        if first == 0:
            oriented = min(oriented, -second % modulus)
    elif first == 0:
        oriented = abs(oriented)
    return abs(first), oriented


def lower_channels(lower, reference):
    side = len(lower) // 2
    mask = (1 << side) - 1
    top, bottom = signs(reference & mask, side), signs(reference >> side, side)
    parts = ([i for i in range(side) if top[i] == bottom[i]],
             [i for i in range(side) if top[i] != bottom[i]])
    sole_right, = [index - side for index in LOWER_OMITTED if index >= side]
    dense_column = signs(lower[LOWER_PIVOT] & mask, side)
    sparse_column = signs(lower[sole_right] & mask, side)
    dense = [dense_column[i] if i not in LOWER_DENSE_HOLES else 0 for i in range(side)]
    sparse = [sparse_column[i] if i in LOWER_SPARSE_SUPPORT else 0 for i in range(side)]

    permutation = [0] * side
    row_signs = [1] * side
    for part_index, rows in enumerate(parts):
        selected = [i for i in rows if sparse[i]]
        unselected = [i for i in rows if not sparse[i]]
        vacancies = [i for i in rows if not dense[i]]
        occupied = [i for i in rows if dense[i]]
        pairs = [*zip(selected, vacancies, strict=True), *zip(unselected, occupied, strict=True)]
        for i, j in pairs:
            permutation[i] = j
            if part_index == 1:
                row_signs[j] = top[i] * top[j]
    assert set(permutation) == set(range(side))

    def action(word):
        result = [0] * side
        for i, j in enumerate(permutation):
            result[j] = row_signs[j] * word[i]
        return result

    reference_channel = [(a - b) // 2 for a, b in zip(top, bottom, strict=True)]
    assert action(reference_channel) == reference_channel
    sparse = action(sparse)
    word_top = pack([a + b for a, b in zip(dense, sparse, strict=True)])
    word_bottom = pack([a - b for a, b in zip(dense, sparse, strict=True)])
    modified = list(lower[:side])
    for old in lower[side:]:
        first = pack(action(signs(old & mask, side)))
        modified.append(first | ((first ^ mask) << side))
    return modified, word_top | (word_bottom << side)


def match_columns(first_a, second_a, first_b, second_b):
    exact = defaultdict(list)
    for j in range(len(first_b)):
        if j not in LOWER_OMITTED:
            exact[signature(first_b[j], second_b[j])].append(j)
    pairs = {}
    for i, (first, second) in enumerate(zip(first_a, second_a, strict=True)):
        possibilities = exact[signature(first, second)]
        if possibilities:
            pairs[i] = possibilities.pop()
    assert len(pairs) == 1083

    modular = defaultdict(list)
    for remaining in exact.values():
        for j in remaining:
            modular[signature(first_b[j], second_b[j], 8)].append(j)
    upper_modular = defaultdict(list)
    for i, (first, second) in enumerate(zip(first_a, second_a, strict=True)):
        if i not in pairs:
            upper_modular[signature(first, second, 8)].append(i)
    for group, top in upper_modular.items():
        bottom = modular[group]
        top.sort(key=lambda i: signature(first_a[i], second_a[i]))
        bottom.sort(key=lambda j: signature(first_b[j], second_b[j]))
        pairs.update(zip(top, bottom, strict=True))
        bottom.clear()
    assert all(not values for values in modular.values())
    return pairs


def verify():
    upper, lower = source_matrices()
    n, m = len(upper), len(lower)
    assert len(set(UPPER_SECOND_FLIPS)) == 32
    assert len(set(LOWER_DENSE_HOLES)) == len(set(LOWER_SPARSE_SUPPORT)) == 34
    u, v = flipped_column(n, UPPER_FLIPS), flipped_column(m, LOWER_FLIPS)
    x = upper[UPPER_PIVOT] ^ sum(1 << i for i in UPPER_SECOND_FLIPS)
    modified_lower, y = lower_channels(lower, v)
    assert verify_orthogonal(m, modified_lower) == 719400
    assert dot(n, u, x) == dot(m, v, y) == 0
    first_a, second_a = ([dot(n, reference, col) for col in upper] for reference in (u, x))
    first_b, second_b = ([dot(m, reference, col) for col in modified_lower] for reference in (v, y))
    assert first_b == [dot(m, v, col) for col in lower]
    omitted = tuple(second_b[j] // 2 for j in LOWER_OMITTED)
    assert omitted == (18, 4, 34, -30) and (omitted, 0) in projection_targets(upper, lower, v)
    assert second_a[0] == second_b[0]
    assert first_a[UPPER_PIVOT] == first_b[LOWER_PIVOT]
    assert second_a[UPPER_PIVOT] == second_b[LOWER_PIVOT] == 1132
    pairs = match_columns(first_a, second_a, first_b, second_b)

    lower_mask = (1 << m) - 1
    columns = []
    for i, column in enumerate(upper):
        j = pairs[i]
        choices = [sign for sign in (1, -1) if first_a[i] + sign * first_b[j] == 0
                   and (second_a[i] + sign * second_b[j]) % 8 == 0]
        sign = min(choices, key=lambda s: abs(second_a[i] + s * second_b[j]))
        low = modified_lower[j] if sign == 1 else modified_lower[j] ^ lower_mask
        columns.append(column | (low << n))
    columns.append(u | (v << n))
    assert len(columns) == 1197 and verify_orthogonal(n + m, columns) == 715806
    new = x | (y << n)
    products = [dot(n + m, new, old) for old in columns]
    assert all(value % 8 == 0 for value in products)
    assert products.count(0) == 1084 and max(map(abs, products)) == 32
    assert sum(value**2 for value in products) == 25984
    packed = "".join(f"{col:x}\n" for col in [*columns, new]).encode("ascii")
    assert sha256(packed).hexdigest() == PACKED_HASH
    print("1197 exact columns; next column: 1084 zeros and 113 nonzero multiples of eight")


if __name__ == "__main__":
    verify()
