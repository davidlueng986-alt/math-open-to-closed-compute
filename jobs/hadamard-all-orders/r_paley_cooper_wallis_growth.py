"""Replay two Cooper--Wallis far lowers with nine exact one-flip lowers."""

from hashlib import sha256
from itertools import combinations

from r_paley_cooper_wallis import HEIGHT, build_pair, build_source
from r_paley_isotropic_code import assemble, half_projections
from verify import verify_orthogonal


ONE_FLIPS = (
    (673, 137), (1159, 899), (83, 287), (751, 364),
    (796, 33), (576, 1023), (773, 162), (1136, 561), (996, 716),
)
SELECTED = int(
    "92715524eeea415d5492aba9267752486ea499dc4933aa92775424e6aa41dd4493bba9"
    "27735cbe45385a8b52ad16e5ea2dcaf45b92e8b607d16e1fa2d8bf45397c8b62cc12e5"
    "3a2440f40bb92563724ae6a491ddc92bbb925777242eac095cd892b1a92173724aeee4"
    "95d5c92bb3105703d3b44f27603f0ed13e9d82f93b45fa260bf4ed03e95a2fd1a44f07"
    "68bf4ed07e9da2fc3b4",
    16,
)
DIGEST = "68c5deb4e7dec31182e99418f99b289558c0515351ba58ca7c44a02990edfc2c"


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
    assert len(set(rows)) == len(set(pivots)) == len(ONE_FLIPS) == 9
    assert set(selected).isdisjoint(pivots)
    assert len(set(selected) - set(old_selected)) == 87
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
    assert len(columns) == 1211 and verify_orthogonal(2396, columns) == 732655
    assert sha256(b"".join(column.to_bytes(300, "little") for column in columns)).hexdigest() == DIGEST
    print(f"Cooper--Wallis 2396 x 1211: two distance-503 far and nine single flips, 732655 exact pairs, SHA256 {DIGEST}")


if __name__ == "__main__":
    verify()
