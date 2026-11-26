"""Replay two Cooper--Wallis far lowers with eight exact one-flip lowers."""

from hashlib import sha256
from itertools import combinations

from r_paley_cooper_wallis import HEIGHT, build_pair, build_source
from r_paley_isotropic_code import assemble, half_projections
from verify import verify_orthogonal


ONE_FLIPS = (
    (673, 137), (1159, 899), (83, 287), (751, 364),
    (796, 33), (576, 1023), (773, 162), (1136, 561),
)
SELECTED = int(
    "92715524eeea415dd413aba92273524a4ea491dc4932aa92775424e6aa41ddc493bba9"
    "27734cba45395a8342ad16e5aa2dcaf45b96e8b60fd06e1fa2d0bf45397c8b62cc12e5"
    "3a2548f44bb92567724ac6a495ddc92bbb92577724aee84958d892b9a92577724aece4"
    "91d5c92bbb105703d3b44f27603f0ed13e9d82f93b45fa260bf4ad03e9da2fd1a44f07"
    "60bf4ed07e9da2fc3b4",
    16,
)
DIGEST = "4d4577f56880c0c6e46a8ee5d1bece0a174ead501e7a5a394f73934284da748f"


def dot(left, right):
    return HEIGHT - 2 * (left ^ right).bit_count()


def sign(word, row):
    return 1 - 2 * ((word >> row) & 1)


def verify():
    source = build_source()
    assert verify_orthogonal(HEIGHT, source) == 714610
    far, old_selected = build_pair(source)
    selected = [j for j in range(HEIGHT) if SELECTED >> j & 1]
    rows, pivots = zip(*ONE_FLIPS, strict=True)
    assert len(selected) == SELECTED.bit_count() == 600
    assert len(set(rows)) == len(set(pivots)) == len(ONE_FLIPS) == 8
    assert set(selected).isdisjoint(pivots)
    assert len(set(selected) - set(old_selected)) == 85
    projections = [half_projections(source, word) for word in far]
    assert [HEIGHT // 2 - max(map(abs, deck)) for deck in projections] == [503, 503]
    assert dot(*far) == 0
    assert all(abs(deck[j]) == 1 for deck in projections for j in selected)
    assert sum(projections[0][j] * projections[1][j] for j in selected) == 0

    for word, deck in zip(far, projections, strict=True):
        for r, g in ONE_FLIPS:
            moment = sum(deck[j] * sign(source[j], r) for j in selected)
            assert moment == sign(source[g], r) * deck[g] - sign(word, r)
    for (r, g), (s, h) in combinations(ONE_FLIPS, 2):
        moment = sum(sign(source[j], r) * sign(source[j], s) for j in selected)
        assert moment == (sign(source[g], r) * sign(source[g], s) +
                          sign(source[h], r) * sign(source[h], s))

    lowers = [*far, *(source[g] ^ (1 << r) for r, g in ONE_FLIPS)]
    columns = assemble(599, source, selected, lowers)
    assert len(columns) == 1210 and verify_orthogonal(2396, columns) == 731445
    assert sha256(b"".join(column.to_bytes(300, "little") for column in columns)).hexdigest() == DIGEST
    print(f"Cooper--Wallis 2396 x 1210: two distance-503 far and eight single flips, 731445 exact pairs, SHA256 {DIGEST}")


if __name__ == "__main__":
    verify()
