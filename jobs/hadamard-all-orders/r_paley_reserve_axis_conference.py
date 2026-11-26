"""Replay the skew-conference axis control and the real 1217 pivot contacts."""

from itertools import combinations, combinations_with_replacement

from r_paley_full92_contrast import AGREE, OPPOSITE
from r_paley_full92_skew import build_source, frame
from r_paley_full92_unrestricted import NEXT_PIVOTS, NEXT_ROOTS, NEXT_SELECTED
from r_paley_isotropic_code import half_projections
from r_paley_punctured_fibre import ALT_SELECTED


def verify_control():
    squares = {i * i % 7 for i in range(1, 7)}
    first = [0] + [1] * 7
    rows = [first]
    for r in range(7):
        rows.append([-1] + [0 if r == s else (1 if (s - r) % 7 in squares else -1)
                            for s in range(7)])
    assert all(rows[i][j] == -rows[j][i] for i in range(8) for j in range(8))
    augmented = [tuple(x + 2 * (i == j) for j, x in enumerate(row))
                 for i, row in enumerate(rows)]
    assert all(sum(a * b for a, b in zip(augmented[i], augmented[j], strict=True)) == 11 * (i == j)
               for i, j in combinations_with_replacement(range(8), 2))
    print("Skew conference control: eight integral axes with squared norm 11")


def verify_contacts(source, mask, rows, pivots, example):
    unused = [j for j in range(1196) if not (mask >> j & 1)]
    assert len(unused) == 596 and len(set(pivots)) == 17
    index = {g: i for i, g in enumerate(unused)}
    axes = []
    for r, g in zip(rows, pivots, strict=True):
        projection = half_projections(source, source[g] ^ (1 << r))
        axis = tuple(599 * (h == g) - projection[h] for h in unused)
        assert axis[index[g]] == 2
        assert all(abs(a) == 1 for j, a in enumerate(axis) if j != index[g])
        axes.append(axis)
    for i, j in combinations_with_replacement(range(17), 2):
        assert sum(a * b for a, b in zip(axes[i], axes[j], strict=True)) == 599 * (i == j)
    equal = []
    for i, j in combinations(range(17), 2):
        first, second = axes[i][index[pivots[j]]], axes[j][index[pivots[i]]]
        if first == second:
            equal.append((pivots[i], pivots[j], first, second))
    assert len(equal) == 16 and example in equal
    print("Seventeen norm-599 axes: sixteen equal-sign pivot contacts, example", example)


def verify():
    verify_control()
    source = build_source()
    rows, pivots = frame()
    fixed_rows = [rows[j] for j in AGREE + OPPOSITE]
    fixed_pivots = [pivots[j] for j in AGREE + OPPOSITE]
    verify_contacts(source, NEXT_SELECTED, fixed_rows + list(NEXT_ROOTS),
                    fixed_pivots + list(NEXT_PIVOTS), (149, 439, -1, -1))
    verify_contacts(source, ALT_SELECTED, fixed_rows + [972, 1013, 1066, 1051, 429],
                    fixed_pivots + [1027, 645, 204, 324, 636], (149, 636, -1, -1))


if __name__ == "__main__":
    verify()
