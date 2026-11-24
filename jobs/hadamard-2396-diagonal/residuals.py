"""Audit remaining linear autocorrelation conditions and the fixed 399-point obstruction."""

import argparse
from fractions import Fraction
import json

from check import EXTENSION, LENGTH, QUOTIENTS, original, paf, words


def representative(s):
    return min(u*s % LENGTH for u in (1, -1, 463, -463, 106, -106))


def add_row(row, basis):
    """Incremental echelon reduction over the rationals, indexed by pivot column."""
    row = {i: Fraction(v) for i, v in row.items() if v}
    while row:
        p = min(row)
        lead = row[p]
        if p not in basis:
            basis[p] = {i: v/lead for i, v in row.items()}
            return
        for i, v in basis[p].items():
            value = row.get(i, 0) - lead*v
            if value:
                row[i] = value
            else:
                row.pop(i, None)


def reduction():
    labels = sorted({representative(s) for s in range(1, LENGTH)})
    columns = {s: i for i, s in enumerate(labels)}
    basis = {}
    # e(0) = 0. All other original errors reduce by reflection and the multiplier.
    for q in QUOTIENTS:
        for t in range(q):
            row = {}
            for s in range(t, LENGTH, q):
                if s:
                    i = columns[representative(s)]
                    row[i] = row.get(i, 0) + 1
            add_row(row, basis)
    projection_rank = len(basis)
    for s in labels:
        if any(q*s % LENGTH == 0 for q in (57, 63)):
            add_row({columns[s]: 1}, basis)
    free = [s for i, s in enumerate(labels) if i not in basis]
    if (len(labels), projection_rank, len(basis), len(free)) != (206, 45, 64, 142):
        raise ValueError("unexpected residual dimension")
    return projection_rank, len(basis), free


def fixed_compression():
    masks = EXTENSION["negative_masks"]
    projected = [[sum(row[j::399]) for j in range(399)] for row in words(masks)]
    if paf(projected, 0) != 2390:
        raise ValueError("shift 399 must already be exact")
    raw = original(masks)
    defects = []
    floor = 0
    for t in range(1, 200):
        error = paf(projected, t) + 6
        lifts = [min(s, LENGTH-s) for s in (t, t+399, t+798)]
        if error != sum(raw[s-1]+2 for s in lifts) or error % 4:
            raise ValueError("399-point projection identity failed")
        defects.append(error)
        # The least sum of three squares at a fixed sum is obtained by balancing.
        a, r = divmod(error//4, 3)
        floor += 16*((3-r)*a*a + r*(a+1)**2)
    result = {"projected_paf_at_one": defects[0]-6, "failed_399_shift_pairs": sum(map(bool, defects)),
              "full_energy_lower_bound_at_fixed_399_margins": floor}
    if tuple(result.values()) != (42, 171, 167520):
        raise ValueError("wrong 399-point certificate statistics")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shifts", action="store_true", help="print a sufficient set of original shifts")
    args = parser.parse_args()
    p, r, free = reduction()
    result = {"projection_rank": p, "rank_with_subgroups": r, "remaining_dimension": len(free),
              **fixed_compression()}
    if args.shifts:
        result["sufficient_original_shifts"] = free
    print(json.dumps(result, indent=2))
