"""Replay the width-1215 Paley extension preserving eleven profile bits."""

import json
from heapq import nlargest
from itertools import combinations

from r_paley_periodic_skew import DATA, check_extension, histogram
from verify import goethals_seidel, length_299_words, rows_from_columns


SELECTED = int(
    "20d2296ff72cbfd17a80177bfa599fa3bac606a643274d8c748920f781b1417446c5"
    "4ad5d6760abc29e9e5a90e8a9ef246e5013660756814442b4bdf6c6636a3ab815dd4"
    "2375d0c2bfcae892aafb915ad9652dcc740f358a22be736639da49a842326c8f168d"
    "ff97c5f548b0594ad4178cf7721d80dda7775d83f8a8609371baaf2af3cea3d512f6"
    "631651c06e1b7b3eb78a0610ee6", 16,
)


def verify_fixed_outer_radius(source, used):
    projected = [row & SELECTED for row in rows_from_columns(1196, source)]
    absolute = [bytearray(1196) for _ in projected]
    for i, j in combinations(range(1196), 2):
        absolute[i][j] = absolute[j][i] = abs(600 - 2 * (projected[i] ^ projected[j]).bit_count())
    assert max(map(max, absolute)) == 88
    assert not any(all(row[i] <= 2 for i in used)
                   for p, row in enumerate(absolute) if p not in used)

    top = [nlargest(9, row) for row in absolute]
    bounds = [
        sum(nlargest(d, (sum(entries[:d - 1]) for entries in top))) // 2
        for d in (3, 5, 7, 9)
    ]
    assert bounds == [217, 639, 1274, 2093]
    assert all(upper < 300 * (d - 1) for d, upper in zip((3, 5, 7, 9), bounds))

    top_nine = [sum(entries) for entries in top]
    anchored = [
        sum(nlargest(10, (2 * weight + top_nine[p] for p, weight in enumerate(row) if p != r)))
        for r, row in enumerate(absolute)
    ]
    assert nlargest(2, anchored) == [6012, 5974]
    print("Fixed width-1215 exterior: any further inner word has signed source distance at least 13")


def verify():
    old = next(r for r in json.loads(DATA.read_text(encoding="ascii"))["extensions"]
               if r["width"] == 1214)
    source = goethals_seidel(length_299_words())
    indices = [j for j in range(1196) if SELECTED >> j & 1]
    assert len(indices) == SELECTED.bit_count() == 600 and indices[0] == 1
    record = dict(
        width=1215,
        inner_rows=old["inner_rows"] + [319],
        inner_columns=old["inner_columns"] + [344],
        gamma_index=indices[0],
        w_columns=indices[1:],
        flipped_source_columns=old["flipped_source_columns"],
        pair_count=737505,
        sha256="54f011a25545b0047624c317c185b22a65f1c5bb36843640a891f474ce6668e2",
    )
    rows, _, selected = check_extension(source, record)
    old_selected = [old["gamma_index"], *old["w_columns"]]
    assert len(set(selected) - set(old_selected)) == 60
    assert histogram(source, rows[:12], selected) == histogram(source, rows[:12], old_selected)
    print("Added source row 319 and reserve 344, preserving all 600 eleven-bit profiles")
    verify_fixed_outer_radius(source, rows)


if __name__ == "__main__":
    verify()
