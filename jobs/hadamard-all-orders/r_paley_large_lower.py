"""Replay two Paley constructions with large nonzero lower inner products."""

from itertools import combinations
from math import comb

from r_paley_anchored_triples import sign
from r_paley_projective_lift import build
from verify import goethals_seidel, length_299_words, rows_from_columns, verify_orthogonal


T = 599
M = 2 * T - 2
MASK = (1 << M) - 1
HALF = (1 << T) - 1

GROUP_X = int(
    "9014d1764434a3ea02cf1b7aedc15043a23134ebf512487808a28bc7d8a26bd6fa5a"
    "d9ab594afa92f58b96cd17cfa36c642f7249ea912e2382ea02558f4ba0ad8740a938"
    "7852a2426c3bfad594a992968250a6eb9070baebbf87b6dd40a34dcee8f7d5f12284"
    "9c32fea0eb4f7645f35feaedec9e2035056d0a746932e8305c939bd08db6156ed1dc"
    "7d15fdaa70b45f5278bf57c787a", 16,
)
GROUP_FLIPS = (
    (80, (280,)), (80, (621,)), (536, (644,)), (1001, (808,)),
    (751, (961,)), (1096, (944,)), (769, (1035,)), (213, (321,)),
)


def rectangle(source, selected, gamma, flips):
    normal = [MASK ^ source[gamma] ^ word for word in source]
    outer, inner = build(T, source, (), w_columns=selected, gamma_index=gamma)
    lower = []
    for g, support in flips:
        assert g != gamma and g not in selected
        assert len(support) == len(set(support))
        orientation = sum(sign(normal[g], r) for r in support)
        assert abs(orientation) == 1
        word = normal[g] if orientation > 0 else normal[g] ^ MASK
        z = word ^ sum(1 << r for r in support)
        assert z.bit_count() == T - 2
        u = tuple(sum(sign(word, r) * sign(normal[j], r) for r in support) for j in selected)
        assert all(abs(s) == 1 for s in u)
        top = sum((s > 0) << j for j, s in enumerate(u))
        inner.append(top | ((top ^ HALF) << T) | (z << (2 * T)) | (3 << (4 * T - 2)))
        lower.append(z)
    return outer + inner, lower


def verify_distance(rows):
    products = tuple(a ^ b for a, b in combinations(rows, 2))
    assert len(products) == comb(M, 2)
    for block in range(24):
        begin, end = M * block // 24, M * (block + 1) // 24
        mask = (1 << (end - begin)) - 1
        projection = ((word >> begin) & mask for word in products)
        keys = {min(word, word ^ mask) for word in projection}
        assert len(keys) == len(products)
    print("Signed row-pair masks: all 714610 classes separate on each of 24 disjoint intervals")


def verify_groups(source):
    gamma = 1176
    selected = tuple(j for j in range(M) if GROUP_X >> j & 1 and j != gamma)
    assert GROUP_X.bit_count() == T + 1 and gamma not in selected
    source_product = sign(source[80], 280) * sign(source[80], 621)
    opposite = next(j for j in selected if sign(source[j], 280) * sign(source[j], 621) != source_product)
    for pivot, large in ((gamma, 1192), (opposite, -1192)):
        w = tuple(j for j in range(M) if GROUP_X >> j & 1 and j != pivot)
        columns, z = rectangle(source, w, pivot, GROUP_FLIPS)
        assert len(columns) == 1208 and verify_orthogonal(4 * T, columns) == 729028
        products = [M - 2 * (a ^ b).bit_count() for a, b in combinations(z, 2)]
        assert products[0] == large
        assert sum(abs(k) == 4 for k in products) == 7
        print(f"Hadamard 2396 × 1208: lower dot {large}, seven lower dots ±4, all 729028 full products zero")


def verify_one_triple(source, rows):
    r, a, b, c = 0, 46, 115, 184
    assert M - 2 * (rows[r] ^ rows[a] ^ rows[b] ^ rows[c]).bit_count() == -444
    g = next(j for j in range(M) if (rows[r] ^ rows[a] ^ rows[b] ^ rows[c]) >> j & 1)
    opposite, same = [], []
    for j in range(M):
        p = sign(source[g], r) * sign(source[j], r)
        q = sum(sign(source[g], k) * sign(source[j], k) for k in (a, b, c))
        if q == -p:
            opposite.append(j)
        elif q == p:
            same.append(j)
    assert len(opposite) == 615 and len(same) == 282
    x = sorted(opposite[:T - 2] + same[:3])
    assert len(x) == T + 1 and g not in x
    flips = ((g, (r,)), (g, (a, b, c)))
    for gamma, large in ((same[0], 1188), (opposite[0], -1188)):
        columns, z = rectangle(source, tuple(j for j in x if j != gamma), gamma, flips)
        assert len(columns) == 1202 and verify_orthogonal(4 * T, columns) == 721801
        assert M - 2 * (z[0] ^ z[1]).bit_count() == large
        print(f"Hadamard 2396 × 1202: same-reserve singleton and triple with lower dot {large}")


if __name__ == "__main__":
    source = goethals_seidel(length_299_words())
    rows = rows_from_columns(M, source)
    verify_distance(rows)
    verify_groups(source)
    verify_one_triple(source, rows)
