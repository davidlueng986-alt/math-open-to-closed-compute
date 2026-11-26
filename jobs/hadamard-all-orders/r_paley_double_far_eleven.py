"""Replay an exact two-far, eleven-single Paley extension at order 2396."""

from hashlib import sha256
from itertools import combinations, combinations_with_replacement

from r_paley_double_far import build_source, dot
from r_paley_double_far_ten import PIVOTS as OLD_PIVOTS
from r_paley_double_far_ten import ROWS as OLD_ROWS
from r_paley_double_far_ten import SELECTED as OLD_SELECTED
from r_paley_double_far_ten import alternate_pair, sign
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from verify import rows_from_columns, verify_orthogonal


ROWS = (*OLD_ROWS, 794)
PIVOTS = (*OLD_PIVOTS, 328)
SELECTED = int(
    "ddffaf6f7f9bfcdffc6df7d7bf6d756fff6bf3dfd53edeb7dfbfe4f26fd77bbb"
    "5fdfbef7b7f400a02501680a404a02c01480b405a00d006802404a02d0168094"
    "05a029016803004a024006803405a02901680a405a02d01680b404202d01680b"
    "005802d016803005a02d014809405a02fe7fb3763afdf7cb966ffabf5ffeacd7"
    "d13ffdafebf367dbfd4eceffa7fdbffdf6abef2f71f",
    16,
)
DIGEST = "649103bb2569e8ffcd93d65ab6338d266eb5de4262a3dd8c7ee3ca8496342706"


def verify():
    source = build_source()
    assert verify_orthogonal(1196, source) == 714610
    far = alternate_pair(source)
    assert dot(*far) == 0
    far_q = [half_projections(source, word) for word in far]
    assert all(min(598 - abs(q) for q in deck) == 483 for deck in far_q)
    old = [j for j in range(1196) if OLD_SELECTED >> j & 1]
    chosen = [j for j in range(1196) if SELECTED >> j & 1]
    for deck in far_q:
        assert all(abs(deck[j]) == 1 for j in chosen)
    assert sum(far_q[0][j] == far_q[1][j] for j in chosen) == 300
    assert len(old) == len(chosen) == 600
    assert (SELECTED & ~OLD_SELECTED).bit_count() == 90
    assert len(set(ROWS)) == len(set(PIVOTS)) == 11
    assert set(PIVOTS).isdisjoint(chosen)

    profiles = [
        *(tuple(-x for x in deck) for deck in far_q),
        *(tuple(sign(col, r) for col in source) for r in ROWS),
    ]
    T = {(0, 1): 0}
    for a, deck in enumerate(far_q):
        for i, (r, g) in enumerate(zip(ROWS, PIVOTS, strict=True), 2):
            T[a, i] = sign(far[a], r) - sign(source[g], r) * deck[g]
    for (i, r), (j, s) in combinations(enumerate(ROWS, 2), 2):
        g, h = PIVOTS[i - 2], PIVOTS[j - 2]
        T[i, j] = sign(source[g], r) * sign(source[g], s)
        T[i, j] += sign(source[h], s) * sign(source[h], r)
    for (i, j), value in T.items():
        assert sum(profiles[i][h] * profiles[j][h] for h in chosen) == value
        if j < len(profiles) - 1:
            assert sum(profiles[i][h] * profiles[j][h] for h in old) == value
        if i:
            assert (value + T[0, i] + T[0, j]) % 4 == 0

    singles = [source[g] ^ (1 << r) for r, g in zip(ROWS, PIVOTS, strict=True)]
    words = far + singles
    columns = assemble(599, source, chosen, words)
    assert len(columns) == 1213 and verify_orthogonal(2396, columns) == 735078
    outside = [col & ((1 << 2394) - 1) for col in columns[:1198]]
    blocks = rows_from_columns(2394, outside)
    assert len(set(blocks)) == 2394 and all(block.bit_count() == 599 for block in blocks)
    assert all((a & b).bit_count() == 598 for a, b in combinations(outside, 2))
    unused = sorted(set(range(1196)) - set(chosen))
    reserves = [tuple(deck[j] for j in unused) for deck in
                (half_projections(source, word) for word in words)]
    assert all(sum(a * b for a, b in zip(u, v, strict=True)) % 599 == 0
               for u, v in combinations_with_replacement(reserves, 2))
    assert rank_mod(reserves, 599) == 13
    digest = sha256(b"".join(col.to_bytes(300, "little") for col in columns)).hexdigest()
    assert digest == DIGEST
    print("Paley double far: 2396 x 1213, two signed distances 483, eleven one-flips, 735078 zero products")
    print("Ten preserved pivots, 90 reselected columns, reserve rank 13, SHA256", digest)


if __name__ == "__main__":
    verify()
