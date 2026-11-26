"""Replay a pair of distance-eleven lower words and two exact local-radius bounds."""

from collections import Counter
from hashlib import sha256
from itertools import combinations

from r_paley_full92_contrast import AGREE, OPPOSITE
from r_paley_full92_skew import build_source, frame
from r_paley_full92_unrestricted import NEXT_SELECTED, verify_rectangle
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from r_paley_periodic_skew import coordinate
from verify import rows_from_columns, verify_orthogonal


ALT_SELECTED = int(
    "4458e72f0edaac1000bb61fbaac98afb0359caa68d6860d26b1755f7c28e7cba"
    "51de06a8f79a6969f3849155d30a9bda6d34531b29d3ef3f658ba39956f8562c"
    "a37943af946629038538be34e5a6745206f6322b6589bca2751dba49564c9605"
    "191c9d38b5b59ca82d96e2df747bc71c7ae173838b8c92ab1576938cc3165c25"
    "a9b9159a4f053db32cd9de0f904381be4c679f34b97",
    16,
)
ALT_DIGEST = "587c9948ff316c54c51849253fe06990abef46691723a4f98fad8d77c2146177"
PAIR_DIGEST = "4b06215fd95ad6cc7465ca48778df57dee39b10a1a4b92adeafb6e2cd6892555"


def read_indices(mask):
    return [j for j in range(1196) if mask >> j & 1]


def punctured_word(source, offset, phase):
    positions = (coordinate(2, residue, phase) for residue in range(13) if residue not in (4, 10))
    flip = sum(1 << r for r in positions)
    reserve = coordinate(0, 2, (offset - phase) % 23)
    assert flip.bit_count() == 11
    return reserve, source[reserve] ^ flip


def verify_short_words(source):
    family = {}
    for offset in (12, 17):
        for phase in range(23):
            reserve, word = punctured_word(source, offset, phase)
            values = half_projections(source, word)
            assert values[reserve] == 587
            assert all(abs(x) <= 11 for j, x in enumerate(values) if j != reserve)
            positive = sum(1 << j for j, x in enumerate(values) if x == 1)
            negative = sum(1 << j for j, x in enumerate(values) if x == -1)
            assert (positive.bit_count(), negative.bit_count()) == (355, 381)
            family[offset, phase] = word, values, positive, negative
    assert len({record[0] for record in family.values()}) == 46

    edges = {}
    for u, v in combinations(family, 2):
        x, _, a, b = family[u]
        y, _, c, d = family[v]
        same, opposite = (a & c) | (b & d), (a & d) | (b & c)
        dot = 1196 - 2 * (x ^ y).bit_count()
        if dot % 4:
            continue
        need_same, need_opposite = 300 - dot // 4, 300 + dot // 4
        if same.bit_count() >= need_same and opposite.bit_count() >= need_opposite:
            edges[u, v] = same, opposite, dot
    assert Counter((a.bit_count(), b.bit_count(), d) for a, b, d in edges.values()) == {
        (306, 306, -12): 46, (306, 306, 0): 46,
    }
    common = Counter(
        ((family[a][2] | family[a][3]) & (family[b][2] | family[b][3]) &
         (family[c][2] | family[c][3])).bit_count()
        for a, b, c in combinations(family, 3) if (a, b) in edges and (a, c) in edges and (b, c) in edges
    )
    assert common == {540: 23}
    u, v = (12, 4), (17, 22)
    assert [punctured_word(source, *key)[0] for key in (u, v)] == [54, 41]
    same, opposite, dot = edges[u, v]
    assert dot == -12
    selected = sorted(read_indices(same)[:303] + read_indices(opposite)[:297])
    assert len(selected) == len(set(selected)) == 600
    words = [family[u][0], family[v][0]]
    columns = assemble(599, source, selected, words)
    assert len(columns) == 1202 and verify_orthogonal(2396, columns) == 721801
    unused = sorted(set(range(1196)) - set(selected))
    code = [tuple(family[key][1][j] for j in unused) for key in (u, v)]
    assert rank_mod(code, 599) == 2
    digest = sha256(b"".join(c.to_bytes(300, "little") for c in columns)).hexdigest()
    assert digest == PAIR_DIGEST
    print("Distance-eleven pair: 2396 x 1202, 721801 zero products, reserve rank 2, SHA256", digest)
    print("46 short words, 92 compatible pairs, 23 candidate triangles with 540 common indices")


def verify_radius(source, selected, powers, expected, upper):
    assert len(selected) == len(set(selected)) == 600
    rows = rows_from_columns(1196, [source[j] for j in selected])
    absolute = [[] for _ in rows]
    shifted = [[] for _ in rows]
    for (i, a), (j, b) in combinations(enumerate(rows), 2):
        correlation = abs(600 - 2 * (a ^ b).bit_count())
        absolute[i].append(correlation)
        absolute[j].append(correlation)
        if correlation > 48:
            shifted[i].append((j, correlation - 48))
            shifted[j].append((i, correlation - 48))
    for row in absolute:
        row.sort(reverse=True)
    for size, bound in zip((3, 5, 7), upper, strict=True):
        maxima = sorted((sum(row[:size - 1]) for row in absolute), reverse=True)
        assert sum(maxima[:size]) == 2 * bound
        assert bound < 300 * (size - 1)
    vector = [1] * len(rows)
    for _ in range(powers):
        vector = [sum(weight * vector[j] for j, weight in neighbors) for neighbors in shifted]
    assert max(vector) == expected < 149**powers
    assert 72 * 48 + 9 * 149 == 4797 < 2 * 2400
    print(f"Fixed exterior: exact B^{powers} row sum certificate, no distances 3, 5, 7, or 9")


def verify():
    source = build_source()
    assert verify_orthogonal(1196, source) == 714610
    verify_short_words(source)
    verify_radius(source, read_indices(NEXT_SELECTED), 19,
                  193130819146243090721935877747526130991104, (312, 885, 1648))
    raw_rows, raw_reserves = frame()
    fixed_rows = [raw_rows[j] for j in AGREE + OPPOSITE]
    fixed_reserves = [raw_reserves[j] for j in AGREE + OPPOSITE]
    alternate = read_indices(ALT_SELECTED)
    width, pairs, _ = verify_rectangle(
        source, fixed_rows + [972, 1013, 1066, 1051, 429],
        fixed_reserves + [1027, 645, 204, 324, 636], alternate, ALT_DIGEST,
    )
    assert width == 1217 and pairs == 739936
    verify_radius(source, alternate, 3, 3299072, (318, 837, 1572))


if __name__ == "__main__":
    verify()
