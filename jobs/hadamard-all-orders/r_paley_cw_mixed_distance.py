"""Replay a distance-503 and distance-nine pair on an exact Cooper--Wallis source."""

from hashlib import sha256
from itertools import combinations_with_replacement

from r_paley_cooper_wallis import COMPRESSED_LOWER, SOURCE_DIGEST, build_source, lift, rotate_long
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from verify import verify_orthogonal


SHORT_RESERVE = 277
FLIPPED_ROWS = (0, 23, 46, 92, 184, 207, 230, 253, 276)
RECTANGLE_DIGEST = "8ae60bc91e90b7f58a6bf19ccb15aa5f981c9002141979f20466003f5d952ff3"
SINGLE_FLIPS = ((856, 987), (720, 475), (244, 674), (236, 160), (9, 1180))
EXTENDED_DIGEST = "1dd6f6a24b341ce68b6bdc2f86f7de0feb5b3d4eb4484f0e3da7a090c1f82ae4"


def verify():
    source = build_source()
    assert verify_orthogonal(1196, source) == 714610
    assert sha256(b"".join(c.to_bytes(150, "little") for c in source)).hexdigest() == SOURCE_DIGEST
    assert all(rotate_long(column) == source[23 * (j // 23) + (j + 1) % 23]
               for j, column in enumerate(source))
    first = lift(COMPRESSED_LOWER[0])
    second = source[SHORT_RESERVE] ^ sum(1 << r for r in FLIPPED_ROWS)
    raw_dot = 1196 - 2 * (first ^ second).bit_count()
    assert raw_dot == 16
    left, right = [half_projections(source, word) for word in (first, second)]
    assert [598 - max(map(abs, deck)) for deck in (left, right)] == [503, 9]
    assert right[SHORT_RESERVE] == 589
    assert all(abs(x) <= 9 for j, x in enumerate(right) if j != SHORT_RESERVE)
    same = [j for j, (a, b) in enumerate(zip(left, right, strict=True)) if abs(a) == 1 and a == b]
    opposite = [j for j, (a, b) in enumerate(zip(left, right, strict=True)) if abs(a) == 1 and a == -b]
    assert (len(same), len(opposite)) == (296, 320)
    selected = sorted(same[:296] + opposite[:304])
    assert len(selected) == len(set(selected)) == 600
    columns = assemble(599, source, selected, [first, second])
    assert len(columns) == 1202 and verify_orthogonal(2396, columns) == 721801
    reserve = sorted(set(range(1196)) - set(selected))
    code = [tuple(p[j] for j in reserve) for p in (left, right)]
    assert all(sum(a * b for a, b in zip(u, v, strict=True)) % 599 == 0
               for u, v in combinations_with_replacement(code, 2))
    assert rank_mod(code, 599) == 2
    assert sha256(b"".join(c.to_bytes(300, "little") for c in columns)).hexdigest() == RECTANGLE_DIGEST
    print("Cooper-Wallis mixed distances 503 and 9: 2396 x 1202, all 721801 products zero")
    print("Joint eligibility 296 + 320, selected 296 + 304, reserve rank 2, SHA256", RECTANGLE_DIGEST)

    assert len({r for r, _ in SINGLE_FLIPS}) == len({g for _, g in SINGLE_FLIPS}) == 5
    assert all(g in reserve for _, g in SINGLE_FLIPS)
    words = [first, second] + [source[g] ^ (1 << r) for r, g in SINGLE_FLIPS]
    projection = [half_projections(source, word) for word in words]
    assert [598 - max(map(abs, p)) for p in projection] == [503, 9, 1, 1, 1, 1, 1]
    extended = assemble(599, source, selected, words)
    assert len(extended) == 1207 and verify_orthogonal(2396, extended) == 727821
    code = [tuple(p[j] for j in reserve) for p in projection]
    assert all(sum(a * b for a, b in zip(u, v, strict=True)) % 599 == 0
               for u, v in combinations_with_replacement(code, 2))
    assert rank_mod(code, 599) == 7
    assert sha256(b"".join(c.to_bytes(300, "little") for c in extended)).hexdigest() == EXTENDED_DIGEST
    print("Same exterior with five single flips: 2396 x 1207, "
          "all 727821 products zero, reserve rank 7, SHA256", EXTENDED_DIGEST)


if __name__ == "__main__":
    verify()
