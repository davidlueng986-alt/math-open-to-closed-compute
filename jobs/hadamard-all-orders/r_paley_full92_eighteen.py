"""Rebuild and check the exact mixed-reserve full92 width-1218 rectangle."""

from collections import Counter
from hashlib import sha256
from itertools import combinations

from r_paley_full92_skew import SOURCE_DIGEST, build_source
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from verify import verify_orthogonal


ROWS = (71, 214, 227, 669, 786, 864, 708, 565, 409, 1163, 1007, 429, 1028, 630, 505, 972, 1013, 464)
PIVOTS = (149, 292, 6, 747, 864, 643, 786, 344, 487, 942, 1085, 751, 416, 708, 307, 935, 599, 473)
SELECTED = int(
    "f58bce166403ab97467a65537a959bdd9450d9878d0cd1b26c1c05b0ee4864a334df"
    "02a945dde809b0ea51631ac69a7aad761dbf3ff2ec1475b9a61c36c067a3b15cd9"
    "a802723b67c73c1777c90e75f0e2b5103a64dca2f1e717945c470b0d6599c4590c"
    "59d19b9464dcc6575439a719a6d9630dcc8cb23f8d620b6a1d26a7970fba51feec"
    "0470f12ccd6e4ab4c8bd57d98e8d3d795",
    16,
)
WARM_SELECTED = int(
    "d5c38b0c64aabc97367bf4537a84cbdd9858c1078d2cd1c2ec385592e64a64c1b0cd"
    "06a9e7dde859b0e85163dac29a6aad361d3f7df0ec12719ba21c34c227a3b35dd928"
    "06723be7c73c9737adae75f0e431143a65dca6dbe515aa5c174a8c6599c459087dd5"
    "db96200c4456603ba749bed965cb5c8c723f8d624b2b1d26f4962fb251fe6d857081"
    "20c96c4ab488b56fdbae9f2d695",
    16,
)
DIGEST = "29dbb183e163906e7595aaed116fe02c414a9a74c6142080008a96d3337d4247"


def source_indices(mask, size):
    return [j for j in range(size) if (mask >> j) & 1]


def source_disagreement(col, r, s):
    return ((col >> r) ^ (col >> s)) & 1


def gram_residuals(source, selected, rows, pivots):
    residuals = {}
    for i, j in combinations(range(len(rows)), 2):
        r, s = rows[i], rows[j]
        hamming = sum(source_disagreement(source[c], r, s) for c in selected)
        target = 299 + source_disagreement(source[pivots[i]], r, s) \
            + source_disagreement(source[pivots[j]], r, s)
        if hamming != target:
            residuals[frozenset((r, s))] = 2 * (target - hamming)
    return residuals


def replay():
    source = build_source()
    size = len(source)
    assert size == 1196
    assert verify_orthogonal(size, source) == 714610
    assert sha256(b"".join(c.to_bytes(150, "little") for c in source)).hexdigest() == SOURCE_DIGEST
    outside = source_indices(SELECTED, size)
    warm = source_indices(WARM_SELECTED, size)
    assert len(outside) == len(warm) == 600
    assert len(set(outside) - set(warm)) == 89
    assert len(set(ROWS)) == len(ROWS) == len(set(PIVOTS)) == 18
    assert set(outside).isdisjoint(PIVOTS)
    assert set(warm).isdisjoint(PIVOTS[:-1] + (477,))
    assert gram_residuals(source, warm, ROWS[:-1] + (1066,), PIVOTS[:-1] + (477,)) == {
        frozenset((864, 1066)): -4,
        frozenset((1013, 630)): -4,
    }

    def profile(j):
        return tuple(source_disagreement(source[j], r, ROWS[0]) for r in ROWS[:15])

    assert Counter(map(profile, outside)) == Counter(map(profile, warm))
    assert gram_residuals(source, outside, ROWS, PIVOTS) == {}
    words = [source[g] ^ (1 << r) for r, g in zip(ROWS, PIVOTS, strict=True)]
    projections = [half_projections(source, word) for word in words]
    for p, g in zip(projections, PIVOTS, strict=True):
        assert p[g] == 597 and all(abs(v) == 1 for j, v in enumerate(p) if j != g)
        assert min(size // 2 - abs(v) for v in p) == 1
    unused = source_indices(((1 << size) - 1) ^ SELECTED, size)
    assert rank_mod([tuple(p[j] for j in unused) for p in projections], 599) == 18
    columns = assemble(599, source, outside, words)
    assert len(columns) == 1218
    assert verify_orthogonal(2396, columns) == 741153
    assert sha256(b"".join(c.to_bytes(300, 'little') for c in columns)).hexdigest() == DIGEST
    print("Full92 width 1218: 741153 zero products, 153 row Gram moments, reserve rank 18")
    print("18 distance-one words, 17 warm row/pivot pairs retained, 89 exterior replacements")
    print("SHA256", DIGEST)


if __name__ == "__main__":
    replay()
