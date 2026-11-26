"""Replay twelve compatible inners obtained by pairing two repeated H92 decks."""

from hashlib import sha256
from itertools import combinations, combinations_with_replacement

from r_paley_full92_skew import build_source, frame
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from r_paley_periodic_skew import check_frame, coordinate
from verify import verify_orthogonal


AGREE = (2, 7, 20, 48, 50, 55, 59, 64)
OPPOSITE = (36, 41, 82, 87)
WHOLE_FIBRES = (12, 5, 7, 8, 9, 11)
PAIR_FIBRES = ((0, 2, 10), (1, 3, 4))
PAIR_INDICES = ((0, 68), (6, 62), (33, 79), (39, 85),
                (62, 6), (68, 0), (79, 33), (85, 39))
DIGEST = "9c32bf6ae25f1b35a0fcb6436ce153a0f88262941f26964072be99b105694c75"


def centre_column(source, rows, j):
    word = sum((source[j] >> r & 1) << i for i, r in enumerate(rows))
    return word if word & 1 else word ^ ((1 << len(rows)) - 1)


def local_index(fibre, j):
    block, phase = divmod(j, 23)
    return coordinate(block, fibre, phase)


def verify():
    source = build_source()
    assert verify_orthogonal(1196, source) == 714610
    rows, pivots = frame()
    chosen_rows = [rows[j] for j in AGREE + OPPOSITE]
    chosen_pivots = [pivots[j] for j in AGREE + OPPOSITE]
    check_frame(source, chosen_rows, chosen_pivots)

    def deck(c):
        return [centre_column(source, rows, local_index(c, j)) for j in range(92)]

    types = [[deck(c) for c in group] for group in PAIR_FIBRES]
    assert all(D == kind[0] for kind in types for D in kind)
    first_block = (1 << 23) - 1
    lookup = [{word & first_block for word in kind[0]} for kind in types]
    assert lookup[0] == lookup[1] and len(lookup[0]) == 92
    contrast = []
    for i in range(92):
        block, phase = divmod(i, 23)
        partner = 23 * (block ^ 2) + (phase if block % 2 else 22 - phase)
        contrast.append(types[0][0][i] ^ types[1][0][partner])
    globally_equal = set(range(23)) | set(range(46, 69)) | {34, 80}
    assert all(sum(diff >> r & 1 for diff in contrast) == (0 if r in globally_equal else 46)
               for r in range(92))

    baseline = [local_index(c, j) for c in WHOLE_FIBRES for j in range(92)]
    assert len(baseline) == 552
    assert all(verify_orthogonal(92, deck(c)) == 4186 for c in WHOLE_FIBRES)
    patch = []
    representatives = []
    for i, j in PAIR_INDICES:
        for c, d in zip(*PAIR_FIBRES, strict=True):
            g, h = local_index(c, i), local_index(d, j)
            a, b = centre_column(source, rows, g), centre_column(source, rows, h)
            diff = a ^ b
            assert diff & first_block == 0
            assert all(diff >> r & 1 == 0 for r in AGREE)
            assert all(diff >> r & 1 == 1 for r in OPPOSITE)
            patch.extend((g, h))
            representatives.append(a)
    assert len(patch) == 48 and len(representatives) == 24
    for side in (AGREE, OPPOSITE):
        assert all(sum(((col >> i) ^ (col >> j)) & 1 for col in representatives) == 12
                   for i, j in combinations(side, 2))

    selected = sorted(baseline + patch)
    assert len(selected) == len(set(selected)) == 600
    assert set(selected).isdisjoint(chosen_pivots)
    words = [source[g] ^ (1 << r) for r, g in zip(chosen_rows, chosen_pivots, strict=True)]
    columns = assemble(599, source, selected, words)
    assert len(columns) == 1212 and verify_orthogonal(2396, columns) == 733866
    point_mask = (1 << 2394) - 1
    outside = [col & point_mask for col in columns[:1198]]
    assert all((a & b).bit_count() == 598 for a, b in combinations(outside, 2))
    unused = sorted(set(range(1196)) - set(selected))
    reserve = [tuple(q[j] for j in unused) for q in (half_projections(source, w) for w in words)]
    assert all(sum(a * b for a, b in zip(u, v, strict=True)) % 599 == 0
               for u, v in combinations_with_replacement(reserve, 2))
    assert rank_mod(reserve, 599) == 12
    digest = sha256(b"".join(col.to_bytes(300, "little") for col in columns)).hexdigest()
    assert digest == DIGEST
    print("Full92 contrast: 2396 x 1212, six whole fibres and 24 physical pairs")
    print("Eight agreeing and four opposite rows, 733866 zero products, reserve rank 12, SHA256", digest)


if __name__ == "__main__":
    verify()
