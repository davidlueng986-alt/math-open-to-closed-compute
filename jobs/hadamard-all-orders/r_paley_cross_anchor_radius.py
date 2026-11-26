"""Verify the cross-anchor physical edit bounds for fixed selector sums."""

from collections import Counter
from itertools import permutations

from r_paley_double_far import SIDE, build_source, fibres
from verify import rows_from_columns


def verify():
    source = build_source()
    masks = [sum(1 << r for r in group) for group in fibres()]
    groups = fibres()
    compressed = [[2 * (source[group[0]] & mask).bit_count() - 23 for group in groups]
                  for mask in masks]
    rows = rows_from_columns(SIDE, source)
    assert all(2 * (source[c] & mask).bit_count() - 23 == compressed[i][j]
               for i, mask in enumerate(masks) for j, group in enumerate(groups) for c in group)
    assert all(2 * (rows[r] & mask).bit_count() - 23 == compressed[i][j]
               for j, mask in enumerate(masks) for i, group in enumerate(groups) for r in group)
    words = [tuple(1 if row[p] > 0 else -1 for row in compressed) for p in (32, 19, 45, 6)]
    decks = [tuple(sum(w * a for w, a in zip(q, col, strict=True))
                   for col in zip(*compressed, strict=True)) for q in words]
    for first, second in permutations(range(4), 2):
        if first // 2 == second // 2:
            continue
        a, b = decks[first], decks[second]
        gate = [j for j, v in enumerate(a) if abs(v) == 2]
        assert sum(abs(b[j]) <= 6 for j in gate) == 20
        assert sum(abs(x) <= 6 and abs(y) <= 6 for x, y in zip(a, b, strict=True)) == 24
        groups_by_height = Counter(abs(b[j]) for j in gate)
        assert {height: count for height, count in groups_by_height.items() if height <= 14} == {2: 16, 6: 4, 10: 8}
        possibilities = {}
        for height in (2, 6, 10):
            active = [j for j in gate if abs(b[j]) == height]
            oriented = [sum((23 + row[j] * q * (b[j] // height)) // 2 for j in active)
                        for q, row in zip(words[second], compressed, strict=True)]
            possibilities[height] = (23 * len(active), max(oriented))
        assert possibilities == {2: (368, 220), 6: (92, 54), 10: (184, 112)}
        for edits, expected in ((2, 422), (4, 552), (6, 583)):
            upper = sum(min(size, edits * per_row // (edits // 2 + (height - 2) // 4))
                        for height, (size, per_row) in possibilities.items()
                        if height <= 2 + 2 * edits)
            assert upper == expected
    print("Cross-anchor radius: all eight orientations; 422 / 552 / 583 at radii 2 / 4 / 6")
    print("Editing both anchors in at most two positions leaves at most 552 common projections")


if __name__ == "__main__":
    verify()
