"""Verify 1197 exact columns and a jointly modulo-eight next column."""

from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198 import pack, projection_targets, signs
from verify import verify_orthogonal


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


def lower_channels(lower, reference, witness):
    side = len(lower) // 2
    mask = (1 << side) - 1
    top, bottom = signs(reference & mask, side), signs(reference >> side, side)
    parts = ([i for i in range(side) if top[i] == bottom[i]],
             [i for i in range(side) if top[i] != bottom[i]])
    sole_right, = [index - side for index in LOWER_OMITTED if index >= side]
    dense_column = signs(lower[witness["lower_pivot"]] & mask, side)
    sparse_column = signs(lower[sole_right] & mask, side)
    holes = set(witness["dense_holes"])
    support = set(witness["sparse_support"])
    dense = [0 if i in holes else dense_column[i] for i in range(side)]
    sparse = [witness["sparse_sign"] * sparse_column[i] if i in support else 0 for i in range(side)]

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


def match_columns(first_a, second_a, first_b, second_b, exact_matches):
    exact = defaultdict(list)
    for j in range(len(first_b)):
        if j not in LOWER_OMITTED:
            exact[signature(first_b[j], second_b[j])].append(j)
    pairs = {}
    for i, (first, second) in enumerate(zip(first_a, second_a, strict=True)):
        possibilities = exact[signature(first, second)]
        if possibilities:
            pairs[i] = possibilities.pop()
    assert len(pairs) == exact_matches

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


def verify_witness(upper, lower, u, v, witness):
    n, m = len(upper), len(lower)
    upper_pivot = witness["upper_pivot"]
    lower_pivot = witness["lower_pivot"]
    assert len(witness["upper_flips"]) == len(set(witness["upper_flips"])) == 32
    for support in (witness["dense_holes"], witness["sparse_support"]):
        assert len(support) == len(set(support)) == 34
        assert all(0 <= i < m // 2 for i in support)
    assert witness["sparse_sign"] in (-1, 1)
    assert all(0 <= i < n for i in witness["upper_flips"])
    x = upper[upper_pivot] ^ sum(1 << i for i in witness["upper_flips"])
    modified_lower, y = lower_channels(lower, v, witness)
    assert verify_orthogonal(m, modified_lower) == 719400
    assert dot(n, u, x) == dot(m, v, y) == 0
    first_a, second_a = ([dot(n, reference, col) for col in upper] for reference in (u, x))
    first_b, second_b = ([dot(m, reference, col) for col in modified_lower] for reference in (v, y))
    assert first_b == [dot(m, v, col) for col in lower]
    omitted = tuple(second_b[j] // 2 for j in LOWER_OMITTED)
    assert omitted == (18, 4, 34, -30) and (omitted, 0) in projection_targets(upper, lower, v)
    assert second_a[0] == second_b[0]
    assert first_a[upper_pivot] == first_b[lower_pivot]
    assert second_a[upper_pivot] == second_b[lower_pivot] == 1132
    pairs = match_columns(first_a, second_a, first_b, second_b, witness["exact_zeros"] - 1)

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
    assert products.count(0) == witness["exact_zeros"]
    assert max(map(abs, products)) == witness["max_abs_dot"]
    assert sum(value**2 for value in products) == witness["squared_residual"]
    packed = "".join(f"{col:x}\n" for col in [*columns, new]).encode("ascii")
    assert sha256(packed).hexdigest() == witness["sha256"]


def verify():
    path = Path(__file__).with_name("stack_1198_joint_data.json")
    witnesses = json.loads(path.read_text(encoding="ascii"))
    upper, lower = source_matrices()
    u = flipped_column(len(upper), UPPER_FLIPS)
    v = flipped_column(len(lower), LOWER_FLIPS)
    for witness in witnesses:
        verify_witness(upper, lower, u, v, witness)
        zeros = witness["exact_zeros"]
        if witness["name"] == "highest_zero_count":
            print(f"1197 exact columns; next column: {zeros} zeros and {1197 - zeros} nonzero multiples of eight")
        else:
            energy = witness["squared_residual"]
            print(f"1198 mod eight alternative: {zeros} zeros; squared residual {energy}")


if __name__ == "__main__":
    verify()
