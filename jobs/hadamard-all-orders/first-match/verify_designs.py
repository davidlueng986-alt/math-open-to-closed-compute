"""Replay the row-pair construction at H92 and an exact one-column obstruction at H28."""

from collections import defaultdict
from itertools import combinations, permutations, product
from math import comb, isqrt
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "closure-dag"))
from verify_pivot import fixed_size_masks, intersections, pivot_matrices, scatter
from verify import check_marginals, determinant, require, verify_orthogonal


def point_columns(blocks, t):
    require(all(0 <= row < 1 << (2*t) for row in blocks), "point labels in range")
    require(len(blocks) == 4*t-2, "number of blocks")
    columns = [sum((row >> j & 1) << i for i, row in enumerate(blocks)) for j in range(2*t)]
    check_marginals(t, columns, [])
    return columns


def pair_certificate(blocks, t, p, q):
    k = t-1
    require(p != q, "distinct seed rows")
    lam = (blocks[p] & blocks[q]).bit_count()
    z = [(row & blocks[p]).bit_count() + (row & blocks[q]).bit_count() - t*(i in (p,q)) - k
         for i, row in enumerate(blocks)]
    require(sum(z) == 2*k and sum(a*(a-1) for a in z) == 2*t*(k-lam), "pair defect")
    return z


def binary_mask(entries):
    require(all(v in (0, 1) for v in entries), "binary certificate")
    return sum(v << i for i, v in enumerate(entries))


def mathon_adjacent(left, right):
    """The 45-vertex Mathon graph in coordinates Z/5 x F3 x F3."""
    i, a, x = left
    j, b, y = right
    delta = (j-i) % 5
    if delta > 2:
        return mathon_adjacent(right, left)
    if delta == 0:
        return a != b and (a+x) % 3 != (b+y) % 3
    if delta == 1:
        return (y-x-a-b) % 3 == 1
    return y != a


def binary_basis(words):
    pivots = {}
    for w in words:
        while w:
            lead = w.bit_length()-1
            if lead not in pivots:
                pivots[lead] = w
                break
            w ^= pivots[lead]
    return list(pivots.values())


def check_residual_words():
    for r in range(1, 8):
        half = (1 << r)-1
        paired = [u | (v << r) for u, v in product(range(half+1), repeat=2)
                  if u.bit_count() == v.bit_count()]
        representatives = {min(w, w ^ ((1 << (2*r))-1)) for w in paired}
        require(2*len(representatives) == len(paired) == comb(2*r, r), "residual word classes")
        basis = binary_basis(paired)
        gram = [sum(((w & v).bit_count() % 2) << j for j, v in enumerate(basis)) for w in basis]
        require(len(binary_basis(gram)) == 2*r-2, "rank of the even residual dot form")
    # Low two bits denote rows containing the center, high two bits the other rows.
    exceptional = [w for w in range(16) if (w >> 2).bit_count() == (w & 3).bit_count()+1]
    permitted = {(a,b) for a,b in combinations(exceptional, 2) if (a & b).bit_count() % 2 == 0}
    require(permitted == {(4,8),(13,14)}, "two missing points must have the same residual type")


def check_three_missing():
    # Bit labels U1,U2,U3,L1,L2,L3. The three missing point labels are interchangeable.
    exceptional = [w for w in range(64) if (w >> 3).bit_count() == (w & 7).bit_count()+1]
    triples = {e for e in combinations(exceptional, 3)
               if all((a & b).bit_count() % 2 == 0 for a,b in combinations(e, 2))}
    require(len(triples) == 26, "all admissible exceptional triples before relabelling")
    coordinates = list(permutations(range(3)))
    orbits = set()
    for representative, size in [((8,16,32),2), ((8,49,50),18), ((25,26,28),6)]:
        orbit = set()
        for upper, lower in product(coordinates, repeat=2):
            order = upper + tuple(i+3 for i in lower)
            words = [sum((w >> i & 1) << j for j,i in enumerate(order)) for w in representative]
            orbit.add(tuple(sorted(words)))
            orbit.add(tuple(sorted(63 ^ ((w >> 3) | ((w & 7) << 3)) for w in words)))
        require(len(orbit) == size and not (orbits & orbit), "residual triple orbit")
        orbits.update(orbit)
    require(triples == orbits, "all exceptional triples are covered by the three representatives")


def check_partial_star(neighbors, outside, r):
    b = len(neighbors)
    d = b-r
    residual = [y >> (2*d) for y in outside[:b]]
    upper = sum(1 << (2*i) for i in range(r))
    known = (1 << d)-1
    for j, word in enumerate(residual):
        require((word & ~upper).bit_count() == (word & upper).bit_count() + (j >= d), "half counts")
        for i in range(j):
            if j < d:
                asymmetry = ((neighbors[i] >> j) ^ (neighbors[j] >> i)) & 1
                require(asymmetry == (word & residual[i]).bit_count() % 2, "paired word Gram")
            elif i >= d:
                require((word & residual[i]).bit_count() % 2 == 0, "exceptional word Gram")
    for i in range(d):
        for j in range(i+1):
            common = (neighbors[i] & neighbors[j] & known).bit_count()
            gram = 4*common + 2*((neighbors[i] >> j & 1) + (neighbors[j] >> i & 1)) + (i == j)
            target = b*(i == j) + b-1 - 2*(residual[i] & residual[j]).bit_count()
            require(gram == target, "near-star determinant Gram")


def check_order92():
    t, n = 23, 92
    points = tuple(product(range(5), range(3), range(3)))
    neighbors = [sum(1 << j for j, right in enumerate(points) if mathon_adjacent(left, right))
                 for left in points]
    for i, row in enumerate(neighbors):
        require(row.bit_count() == 22 and not (row >> i & 1), "Mathon degree and loops")
        for j in range(i):
            edge = row >> j & 1
            require(edge == (neighbors[j] >> i & 1), "undirected edges")
            require((row & neighbors[j]).bit_count() == 11-edge, "Mathon common neighbors")

    # Inner labels 0..44 are ordinary points. Bit 45 is the common exchanged point.
    blocks = [row | bit for i, row in enumerate(neighbors) for bit in (1 << 45, 1 << i)]
    outside = point_columns(blocks, t)
    for r in range(1,8):
        check_partial_star(neighbors, outside, r)
    inside = [binary_mask(pair_certificate(blocks, t, 2*i, 2*i+1)) for i in range(45)]
    require(len(set(inside)) == 45, "distinct certificates in the star")
    check_marginals(t, outside, inside)
    require(all((x & y).bit_count() == t-1 for x in inside for y in outside), "mixed counts")
    columns = [(1 << n)-1] + [(y << 2) | 1 for y in outside] + [(x << 2) | 3 for x in inside]
    require(len(columns) == n, "all square columns")
    print(f"H92: 45 row-pair certificates, all {verify_orthogonal(n, columns):,} square column pairs orthogonal")


# Bit j marks point j. These are the 26 lower blocks extracted from normalized Paley II H28.
H28_BLOCKS = (
    9123, 9767, 3469, 6810, 5399, 2831, 13372, 10810, 5782, 11436, 6457, 12721, 16256,
    16192, 7267, 6374, 12877, 9562, 10453, 12491, 1012, 1514, 10582, 4972, 1753, 3697,
)
TRADES = ((2, 11, 16, 25), (3, 9, 17, 23), (0, 8, 14, 22))


def trade(blocks, indices):
    a, b, c, d = (blocks[i] for i in indices)
    require(a ^ b ^ c ^ d == 0, "every point occurs evenly on the four rows")
    # On these four rows, switch every column of weight two to its complement.
    flip = (a | b | c | d) ^ (a & b & c & d)
    return [row ^ flip if i in indices else row for i, row in enumerate(blocks)]


def all_first(t, outside):
    a, b, pos, neg = pivot_matrices(t, outside, 0)
    options = tuple(fixed_size_masks(2*t-1, t-1))
    by_signature = defaultdict(list)
    for v in options:
        by_signature[intersections(b, v)].append(v)
    return [scatter(u, pos) | scatter(v, neg) for u in options
            for v in by_signature.get(intersections(a, u), ())]


def check_order28():
    t = 7
    blocks = H28_BLOCKS
    for j, expected in enumerate((13, 13, 5, 1)):
        if j:
            blocks = trade(blocks, TRADES[j-1])
        outside = point_columns(blocks, t)
        choices = all_first(t, outside)
        require(len(choices) == len(set(choices)) == expected, "all exact first columns")
        for x in choices:
            require(x.bit_count() == 12 and intersections(outside, x) == (6,)*14, "direct counts")
        z = binary_mask(pair_certificate(blocks, t, 12, 13))
        require(z in choices, "row-pair witness belongs to atlas")
        require(all(x == z or (x & z).bit_count() == t-2 for x in choices), "universal vertex")
    selected = [0, 2, 3, 8, 9, 11, 14, 16, 17, 22, 23, 25]
    require(choices == [sum(1 << i for i in selected)], "unique final column")
    print(f"H28: all {comb(13,6):,} subsets per side at each step, first-column counts 13, 13, 5, 1")


def check_order2396():
    b = 1197
    require(3**2 * 7 * 19 == b, "factorization")
    require(all(isqrt(b-i*i)**2 != b-i*i for i in range(isqrt(b)+1)), "sum of two squares")
    k, d = 598, b-2
    cases = 0
    for matched in range(2, k//2+1, 2):
        crossed = k-matched
        counts = {0: k//2-1, 15: k//2, 5: matched//2, 10: matched//2,
                  6: crossed//2, 9: crossed//2}
        require(sum(counts.values()) == d, "ordinary point totals")
        words = [(n, [1] + [w >> j & 1 for j in range(4)]) for w,n in counts.items()]
        scale = [b-1,-2,-2,-2,-2]
        small = [[b*(i==j) + scale[i]*sum(n*w[i]*w[j] for n,w in words)
                  for j in range(5)] for i in range(5)]
        target = b*(2*matched+1)*(2*crossed+1)
        require(determinant(small) == d*d*target, "exact compressed determinant")
        require(isqrt(target)**2 != target, "squared determinant obstruction")
        cases += 1
    require(cases == 149, "all unordered active class sizes")
    print("H2396: all 149 degree-1195 determinants fail; star degrees 1195, 1196 and 1197 excluded")


if __name__ == "__main__":
    check_residual_words()
    check_three_missing()
    check_order28()
    check_order92()
    check_order2396()
