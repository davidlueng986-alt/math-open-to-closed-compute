"""Replay the ternary-channel candidate and export the exact pivot search input."""

import argparse
import struct
from itertools import permutations, product
from math import isqrt
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from verify import verify_orthogonal


CHANNEL_PIVOT = 1
CHANNEL_ZERO_ROWS = (
    0, 30, 46, 51, 63, 76, 91, 92, 115, 118, 170, 184, 210, 218, 274, 302, 329,
    424, 428, 433, 434, 438, 460, 492, 512, 520, 523, 538, 543, 555, 560, 564, 577, 595,
)
CHANNEL_SECOND_ENTRIES = (
    (70, 1), (102, 1), (104, -1), (157, -1), (169, 1), (201, 1), (208, -1),
    (213, -1), (229, -1), (231, -1), (246, -1), (261, -1), (279, -1), (291, -1),
    (307, -1), (321, -1), (331, 1), (336, -1), (360, 1), (369, 1), (376, 1),
    (384, -1), (386, 1), (421, 1), (438, 1), (466, -1), (474, -1), (486, 1),
    (509, -1), (523, -1), (537, -1), (546, 1), (549, -1), (573, -1),
)


def half_dot(size, left, right):
    return size // 2 - (left ^ right).bit_count()


def projection_targets(upper, lower, reference, omitted=LOWER_OMITTED):
    """Enumerate omitted half-dots and the required lower mutual inner product."""
    size = len(lower)
    square_norm = (size**2 - len(upper)**2) // 4
    scale = (size + len(upper)) // 4
    first = tuple(half_dot(size, reference, lower[index]) for index in omitted)
    targets = set()
    limit = isqrt(square_norm)
    for a in range(limit + 1):
        for b in range(a, limit + 1, 2):
            for c in range(b, limit + 1, 2):
                remainder = square_norm - a**2 - b**2 - c**2
                if remainder < c**2:
                    break
                d = isqrt(remainder)
                if d**2 != remainder or (d ^ a) & 1:
                    continue
                for order in set(permutations((a, b, c, d))):
                    for signs in product((-1, 1), repeat=4):
                        projection = tuple(x * sign for x, sign in zip(order, signs, strict=True))
                        inner = sum(x * y for x, y in zip(first, projection, strict=True))
                        if inner % scale:
                            continue
                        mutual = inner // scale
                        if abs(mutual) <= 4 and mutual % 4 == 2 * (a & 1):
                            targets.add((projection, mutual))
    assert len(targets) == 46
    assert sum(mutual == 0 for _, mutual in targets) == 12
    return sorted(targets)


def export_search(path, upper, lower, u, v, targets, omitted=LOWER_OMITTED):
    with path.open("wb") as stream:
        stream.write(struct.pack("<7i", len(upper), len(lower), *omitted, len(targets)))
        for projection, mutual in targets:
            stream.write(struct.pack("<5i", *projection, mutual))
        for word in (u, v, *upper, *lower):
            stream.write(word.to_bytes(19 * 8, "little"))


def signs(word, size):
    return [1 if word >> i & 1 else -1 for i in range(size)]


def pack(word):
    assert all(value in (-1, 1) for value in word)
    return sum((value == 1) << index for index, value in enumerate(word))


def verify_ternary(lower, v, targets):
    side = len(lower) // 2
    mask = (1 << side) - 1
    top, bottom = signs(v & mask, side), signs(v >> side, side)
    groups = ([i for i in range(side) if top[i] == bottom[i]],
              [i for i in range(side) if top[i] != bottom[i]])
    assert [len(group) for group in groups] == [566, 34]
    assert all(top[i] == 1 for i in groups[0])
    assert sum(top[i] == 1 for i in groups[1]) == 17

    pivot = signs(lower[CHANNEL_PIVOT] & mask, side)
    channel0 = [0 if index in CHANNEL_ZERO_ROWS else value for index, value in enumerate(pivot)]
    nonzero = dict(CHANNEL_SECOND_ENTRIES)
    assert len(nonzero) == len(CHANNEL_SECOND_ENTRIES) == len(CHANNEL_ZERO_ROWS) == 34
    channel1 = [nonzero.get(i, 0) for i in range(side)]
    assert any(a and b for a, b in zip(channel0, channel1, strict=True))

    # The second-channel permutation places its support at the first-channel vacancies.
    permutation = [0] * side
    row_signs = [1] * side
    for group_index, group in enumerate(groups):
        active = [i for i in group if channel1[i]]
        inactive = [i for i in group if not channel1[i]]
        vacancies = [i for i in group if not channel0[i]]
        occupied = [i for i in group if channel0[i]]
        pairs = [*zip(active, vacancies, strict=True), *zip(inactive, occupied, strict=True)]
        for i, j in pairs:
            permutation[i] = j
            if group_index == 1:
                row_signs[j] = top[i] * top[j]
    assert set(permutation) == set(range(side))

    def permute(values):
        result = [0] * side
        for i, j in enumerate(permutation):
            result[j] = values[i] * row_signs[j]
        return result

    reference_channel = [(a - b) // 2 for a, b in zip(top, bottom, strict=True)]
    assert permute(reference_channel) == reference_channel
    channel1 = permute(channel1)
    y_top = pack([a + b for a, b in zip(channel0, channel1, strict=True)])
    y_bottom = pack([a - b for a, b in zip(channel0, channel1, strict=True)])
    y = y_top | (y_bottom << side)
    modified_lower = list(lower[:side])
    for col in lower[side:]:
        new_half = pack(permute(signs(col & mask, side)))
        modified_lower.append(new_half | ((new_half ^ mask) << side))

    size = len(lower)
    assert verify_orthogonal(size, modified_lower) == 719400
    assert [half_dot(size, v, col) for col in modified_lower] == [half_dot(size, v, col) for col in lower]
    omitted = tuple(half_dot(size, y, modified_lower[j]) for j in LOWER_OMITTED)
    assert omitted == (-34, -30, 18, -4) and (omitted, 0) in targets
    assert half_dot(size, y, v) == 0
    assert half_dot(size, y, modified_lower[CHANNEL_PIVOT]) == 566
    print("1198 ternary bridge: exact lower sign source, omitted half-dots, and mutual orthogonality")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export", type=Path, help="output for the C++ pivot-radius verifier")
    output = parser.parse_args().export
    upper, lower = source_matrices()
    u = flipped_column(len(upper), UPPER_FLIPS)
    v = flipped_column(len(lower), LOWER_FLIPS)
    targets = projection_targets(upper, lower, v)
    verify_ternary(lower, v, targets)
    if output is not None:
        export_search(output, upper, lower, u, v, targets)


if __name__ == "__main__":
    main()
