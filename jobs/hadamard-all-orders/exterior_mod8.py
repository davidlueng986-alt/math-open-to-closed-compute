"""Verify a joint exterior-stack lift satisfying all Gram congruences modulo eight."""
import json
from pathlib import Path

from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, exterior_sources
from verify import require, verify_orthogonal


def lift_upper(syndrome, top_negative):
    """Lift the retained binary column syndrome to all four possible upper halves."""
    require(len(syndrome) == TOP - 3 and len(top_negative) == TOP, "upper core dimensions")
    core_rows = (1 << TOP) - 2
    tail_parity = sum(syndrome) % 2
    candidates = set()
    for first in (0, 1):
        complete = (0, first, (tail_parity + first) % 2, *syndrome)
        representative = 0
        for flag, column in zip(complete, top_negative, strict=True):
            if flag:
                representative ^= column
        candidates.update((representative, representative ^ core_rows))
    require(len(candidates) == 4, "four different affine binary lifts")
    return candidates


def main():
    path = Path(__file__).with_suffix(".json")
    certificate = json.loads(path.read_text())
    top, bottom = exterior_sources()
    lower = [col for j, col in enumerate(bottom) if j not in LOWER_OMISSIONS]
    permutation = certificate["lower_permutation"]
    require(sorted(permutation) == list(range(TOP - 3)), "permutation of all retained columns")
    old_positive = [col | (lower[j] << TOP) for col, j in zip(top[3:], permutation, strict=True)]
    require(verify_orthogonal(ORDER, old_positive) == 711028, "all retained column pairs")
    rows_mask = (1 << ORDER) - 1
    old = [col ^ rows_mask for col in old_positive]
    new = [int(col, 16) for col in certificate["new_negative_columns"]]
    require(len(new) == 5 and all(0 <= col <= rows_mask for col in new), "full sign column width")
    require(all(col.bit_count() == ORDER // 2 for col in old + new), "all columns balanced")
    loads = [sum(col >> i & 1 for col in old + new) for i in range(ORDER)]
    require(loads[0] == 0 and loads[TOP] == ORDER // 2, "opposite border rows")
    require(all(loads[i] == ORDER // 4 for i in range(ORDER) if i not in (0, TOP)),
            "all other rows balanced")

    mixed = [ORDER - 2 * (a ^ b).bit_count() for a in old for b in new]
    gram = [ORDER - 2 * (a ^ b).bit_count() for j, b in enumerate(new) for a in new[:j]]
    require(len(mixed) == 5965 and len(gram) == 10, "all relevant pairs covered")
    require(all(dot % 8 == 0 for dot in mixed + gram), "all old/new and new/new dots vanish modulo eight")
    require(mixed.count(0) == 417 and gram == [-64, 112, 0, -104, 40, 16, 56, -56, 0, 0],
            "exact remaining inner products on this witness")

    top_mask = (1 << TOP) - 1
    bottom_mask = (1 << BOTTOM) - 1
    top_negative = [col ^ top_mask for col in top]
    lower_negative = [lower[j] ^ bottom_mask for j in permutation]
    for column in new:
        below = column >> TOP
        syndrome = tuple(1 - (below & col).bit_count() % 2 for col in lower_negative)
        candidates = lift_upper(syndrome, top_negative)
        require((column & top_mask) in candidates, "upper half recovered from the lower half")
        require(all(tuple((upper & col).bit_count() % 2 for col in top_negative[3:]) == syndrome
                    for upper in candidates), "all recovered upper syndromes")

    # A full integer lift keeping these upper signs would force two negative
    # squared norms for the contrast of each of the paired new columns.
    upper_positive = [top_mask ^ (col & top_mask) for col in new]
    contrasts = []
    for i, j in ((1, 2), (3, 4)):
        left, right = upper_positive[i], upper_positive[j]
        gaps = [(omit ^ right).bit_count() - (omit ^ left).bit_count() for omit in top[1:3]]
        distance = (left ^ right).bit_count()
        contrasts.append(ORDER * (2 * BOTTOM - 4 * distance) + 4 * sum(gap * gap for gap in gaps))
    require(contrasts == [-3339776, -3350912], "exact lift requires changing the upper signs")

    print("n=2396: exact margins and all 5965 mixed / 10 new dots zero modulo eight")
    print(f"n=2396: {mixed.count(0)} exact mixed zeros; {gram.count(0)} exact new/new zeros; new/new dots {gram}")
    print(f"n=2396: fixed upper witness fails the required real Gram contrasts {contrasts}")


if __name__ == "__main__":
    main()
