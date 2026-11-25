"""Exact two-direction Parseval bounds for a five-column exterior stack."""
from itertools import product
import json
from pathlib import Path

from five_column_constraints import ORDER, BOTTOM, TOP, exterior_sources
from verify import require


THRESHOLD = 955
MAX_ERRORS = 52
COINCIDENT_GROUP = 299
OPPOSITE_GROUP = 598


def convex_hull(points):
    """Integer vertices; a convex polynomial attains its maximum at a vertex."""
    points = sorted(set(points))
    vertices = []
    for order in (points, reversed(points)):
        chain = []
        for p in order:
            while len(chain) >= 2:
                o, a = chain[-2:]
                turn = (a[0] - o[0]) * (p[1] - o[1]) - (a[1] - o[1]) * (p[0] - o[0])
                if turn > 0:
                    break
                chain.pop()
            chain.append(p)
        vertices.extend(chain[:-1])
    return vertices or points


def error_vertices(opposite):
    same = THRESHOLD - opposite
    target = ORDER * THRESHOLD - BOTTOM * (ORDER // 2)
    return convex_hull(
        (a, b) for a in range(MAX_ERRORS + 1) for b in range(MAX_ERRORS + 1 - a)
        if 2 * ((same - 2 * a)**2 + (opposite - 2 * b)**2) >= target
    )


def check_wide_pairs():
    max_gap = 2 * (352**2 + 598**2) - (ORDER * 950 - BOTTOM * (ORDER // 2))
    require(max_gap == 124416 < 8 * 53 * (352 - 53), "one-pair orientation error bound")

    total = 2 * THRESHOLD
    maximum_same_sum = total - 2 * OPPOSITE_GROUP
    same_omission = (ORDER * BOTTOM - ORDER * (3 * total - 2 * (TOP - 1) - 8 * MAX_ERRORS)
                     + 2 * (maximum_same_sum**2 + (2 * OPPOSITE_GROUP)**2))
    require(same_omission == -250280, "same omitted direction is impossible")

    max_same_total = 3 * COINCIDENT_GROUP - 1
    min_opposite_total = total - max_same_total
    min_opposite = min_opposite_total - OPPOSITE_GROUP
    vertices = {n: error_vertices(n) for n in range(min_opposite, OPPOSITE_GROUP + 1)}
    best = None
    for n1 in vertices:
        for n2 in range(n1, OPPOSITE_GROUP + 1):
            opposite_total = n1 + n2
            if opposite_total < min_opposite_total:
                continue
            base_norm = total + 2 * (opposite_total - OPPOSITE_GROUP - COINCIDENT_GROUP)
            for (a1, b1), (a2, b2) in product(vertices[n1], vertices[n2]):
                minus_errors = b1 + b2
                u = n2 - n1 - 2 * a1 + 2 * a2
                v = opposite_total - 2 * minus_errors
                upper = ORDER * (BOTTOM - base_norm + 4 * minus_errors) + 2 * (u * u + v * v)
                best = upper if best is None else max(best, upper)
    require(best == -10928, "different omitted directions are impossible")
    print(f"n=2396: no exact five-column completion has two disjoint upper distances >= {THRESHOLD}; "
          f"Gram upper bounds {same_omission}, {best}")


def check_modular_supports():
    certificate = json.loads(Path(__file__).with_name("exterior_mod8.json").read_text())
    top, _ = exterior_sources()
    mask = (1 << TOP) - 1
    new = [int(col, 16) & mask for col in certificate["new_negative_columns"]]
    support1, support2 = new[1] ^ new[2], new[3] ^ new[4]
    opposite = top[1] ^ top[2]
    require((support1.bit_count(), support2.bit_count()) == (950, 950), "two modular-witness distances")
    require(all((support & opposite).bit_count() == 532 for support in (support1, support2)),
            "opposite-sign rows in each support")
    common = support1 & support2
    require((common.bit_count(), (common & opposite).bit_count()) == (760, 477),
            "two modular-witness supports overlap")
    gap = 2 * (418**2 + 532**2) - (950 * ORDER - BOTTOM * (ORDER // 2))
    require(gap == 76896 < 8 * 25 * (418 - 25), "each support allows at most 24 orientation errors")
    same_omission = ORDER * (BOTTOM - 1900 - 2 * (760 - 2 * 48)) + 8 * (418**2 + 532**2)
    different_omissions = ORDER * (BOTTOM - 2288) + 2 * 1064**2 + 1072 * 48 + 8 * 48**2
    require((same_omission, different_omissions) == (-1197104, -272768),
            "both orientation cases fail for these supports")
    print("n=2396: the two published modular pair supports cannot be completed by any reorientation")


if __name__ == "__main__":
    check_wide_pairs()
    check_modular_supports()
