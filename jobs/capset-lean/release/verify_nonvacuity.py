#!/usr/bin/env python3
"""Recheck the two finite examples independently of Lean, using Python stdlib.

This checks concrete mathematical data.  It does not replace Lean compilation
or its axiom audit, and it is not a proof of a seven-dimensional numerical bound.
"""

from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def points(data, key, dimension):
    raw = data[key]
    result = {tuple(point) for point in raw}
    require(len(result) == len(raw), f"{key}: repeated point")
    require(all(len(point) == dimension and all(x in range(3) for x in point)
                for point in result), f"{key}: invalid F3 point")
    return result


def add(a, b):
    return tuple((x + y) % 3 for x, y in zip(a, b))


def neg(a):
    return tuple(-x % 3 for x in a)


def cap_pair_checks(cap):
    count = 0
    for a, b in combinations(sorted(cap), 2):
        count += 1
        require(neg(add(a, b)) not in cap, f"forbidden cap triple: {a}, {b}")
    return count


def reps(a_set, b_set, target):
    return {(a, b) for a in a_set for b in b_set if add(a, b) == target}


def sums(a_set, b_set):
    return {add(a, b) for a in a_set for b in b_set}


def layered(a_set, b_set, c_set):
    return {a + (0,) for a in a_set} | {b + (1,) for b in b_set} | {
        c + (2,) for c in c_set}


def check_five_point_cap():
    data = json.loads((HERE / "NONVACUITY_AUDIT.json").read_text())
    a_set, b_set = (points(data, name, 2) for name in ("A", "B"))
    da, db = (points(data, name, 2) for name in ("deleted_A", "deleted_B"))
    a0, b0, c_set = (points(data, name, 2) for name in ("A0", "B0", "C"))
    cap = points(data, "actual_cap_K_in_G_times_F3", 3)
    target = tuple(data["target"])
    require(a_set - da == a0 and b_set - db == b0, "retained slices mismatch")
    require(len(da) == len(db) == 2, "expected two actual deletions per side")
    require(da <= a_set and db <= b_set and c_set, "non-vacuity failed")
    require(cap == layered(a0, b0, c_set), "layered cap mismatch")
    cap_pair_checks(a_set)
    cap_pair_checks(b_set)
    require(cap_pair_checks(cap) == data["cap_K_pair_checks"] == 10,
            "five-point cap pair count mismatch")
    original = reps(a_set, b_set, target)
    recorded = {(tuple(a), tuple(b)) for a, b in data["original_ordered_representations"]}
    require(original == recorded and len(original) == 4, "four representations mismatch")
    require(not reps(a0, b0, target) and data["surviving_representations"] == [],
            "target is not a deletion hole")
    require(target in {neg(c) for c in c_set}, "target is not negative third slice")
    a1, a2 = sorted(da)
    b1, b2 = sorted(db)
    left = {add(a1, b) for b in b_set} & {add(a2, b) for b in b_set}
    right = {add(b1, a) for a in a_set} & {add(b2, a) for a in a_set}
    require(left == points(data, "left_double_translate_intersection", 2),
            "left overlap mismatch")
    require(right == points(data, "right_double_translate_intersection", 2),
            "right overlap mismatch")
    require(target in left & right, "four-representation intersection failed")
    return {"status": "PASS", "cap_size": len(cap), "representations": len(original)}


def check_eighteen_point_cap():
    data = json.loads((HERE / "SUMSET_STABILITY_NONVACUITY_AUDIT.json").read_text())
    a_set, b_set = (points(data, name, 3) for name in ("raw_A", "raw_B"))
    da, db = (points(data, name, 3) for name in ("deleted_A", "deleted_B"))
    a0, b0 = (points(data, name, 3) for name in ("retained_A", "retained_B"))
    c_set = points(data, "third_slice_C", 3)
    cap = points(data, "actual_cap_K_in_F3_4", 4)
    require(a_set == {(x, y, (x*x + y*y) % 3) for x, y in product(range(3), repeat=2)},
            "quadratic cap formula mismatch")
    require(b_set == {neg(a) for a in a_set}, "reflected cap mismatch")
    require(da <= a_set and db <= b_set and len(da) == len(db) == 1,
            "expected one actual deletion on each side")
    require(a_set - da == a0 and b_set - db == b0, "retained slices mismatch")
    require(cap == layered(a0, b0, c_set), "layered cap mismatch")
    checks = {"A": cap_pair_checks(a_set), "B": cap_pair_checks(b_set),
              "actual_cap_K": cap_pair_checks(cap)}
    require(checks == data["pair_checks"], "cap pair counts mismatch")
    universe = set(product(range(3), repeat=3))
    multiplicity = {t: len(reps(a_set, b_set, t)) for t in universe}
    histogram = {str(k): v for k, v in sorted(Counter(multiplicity.values()).items())}
    require(histogram == data["multiplicity_distribution_in_all_G"], "spectrum mismatch")
    require(len(da) + len(db) == data["total_deleted_endpoints"] < data["k"],
            "deletions do not satisfy the strict bound")
    require(all(r == 0 or r >= data["k"] for r in multiplicity.values()),
            "attained-sum multiplicity bound failed")
    before, after = sums(a_set, b_set), sums(a0, b0)
    require(before == after, "sumset stability failed")
    require(len(before) == data["sumset_size_before"] == 25 and
            len(after) == data["sumset_size_after"], "sumset sizes mismatch")
    require(c_set and all(neg(c) not in before for c in c_set),
            "nonempty third slice does not avoid completed sums")
    return {"status": "PASS", "cap_size": len(cap), "sumset_size": len(before),
            "multiplicity_distribution": histogram, "pair_checks": checks}


if __name__ == "__main__":
    print(json.dumps({"five_point_cap": check_five_point_cap(),
                      "eighteen_point_cap": check_eighteen_point_cap()}, indent=2))
