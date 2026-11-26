"""Replay one period-23 far inner column on the exact R(599) exterior."""

from collections import Counter
from hashlib import sha256

from r_paley_isotropic_code import assemble, half_projections, rank_mod

from r_paley_multiflip_inner import replay
from verify import goethals_seidel, length_299_words, verify_orthogonal

SIDE = 1196
BLOCK = 299
PERIOD = 23
PIVOTS = (11, BLOCK + 11)
PERIODS = (
    "+-+---+---+++---+---+-+",
    "---++--+--+-+--+--++---",
    "---+-+++-+++++-+++-+---",
    "-+-+--+++-----+++--+-+-",
)
DECK = {2: 49, 6: 25, 10: 10, 14: 4, 26: 2, 230: 2}
DIGEST = "e4dec8115108d6c4d4b222ed3ad5c1c82a935d5a588e7d165fd4b92d0c2e869f"


MIXED_SOURCE_MASK = int(
    "3f83f87e0770fe0fe1fc1fc2f83787f07d0de0ee1bc1fc3f82787e07f0fe0fe1d"
    "c0fc3f03f821742042e84085d0810ba1021742042e84085c0810ba1021742042e"
    "84085d0810ba102054213eaf925d5d04f2be49f57c93caf927d5f24fabe49f56c"
    "93eaf927d5b24dabe49b57c93e2f927d4e24fabe49f57c93aaf927d5724fabe49"
    "f56c93eaf927c5f247abe49f57c03eab927d5f2", 16,
)
MIXED_ROWS = (105, 1169, 597, 598, 585, 1189)
MIXED_PIVOTS = (30, 1150, 529, 751, 553, 1081)
MIXED_DIGEST = "5d7f1d5646d19362cd73f8a6ba03c4a9d91ad123497f18bbfb3a86ef1d30d106"


def row_fibres():
    return tuple(
        tuple(block * BLOCK + r for r in range(residue, BLOCK, PERIOD))
        for block in range(4)
        for residue in range(PERIOD)
    )


def raw_word(source, fibres):
    signs = []
    for rows in fibres:
        signed_sum = sum(
            2 * ((source[col] >> r) & 1) - 1
            for col in PIVOTS
            for r in rows
        )
        assert abs(signed_sum) in (4, 6)
        signs.append("+" if signed_sum > 0 else "-")
    assert "".join(signs) == "".join(PERIODS)
    return sum(1 << r for s, rows in zip(signs, fibres, strict=True) if s == "+" for r in rows)


def verify():
    source = goethals_seidel(length_299_words())
    assert verify_orthogonal(SIDE, source) == 714610
    fibres = row_fibres()
    assert len(fibres) == 92 and all(len(rows) == 13 for rows in fibres)
    assert sorted(r for rows in fibres for r in rows) == list(range(SIDE))
    raw = raw_word(source, fibres)
    projections = [SIDE - 2 * (raw ^ col).bit_count() for col in source]
    assert all(p % 4 == 2 for p in projections)
    assert all(len({projections[c] for c in cols}) == 1 for cols in fibres)
    assert Counter(abs(projections[cols[0]]) for cols in fibres) == DECK
    assert projections[PIVOTS[0]] == max(map(abs, projections)) == 230
    nearest_distance = (SIDE - max(map(abs, projections))) // 2
    changed = raw ^ source[PIVOTS[0]]
    positions = [r for r in range(SIDE) if (changed >> r) & 1]
    assert len(positions) == nearest_distance == 483
    eligible = [j for j, p in enumerate(projections) if abs(p) == 2]
    assert len(eligible) == 637
    fixture = {
        "K": eligible[:600],
        "width": 1201,
        "nonflip": 1,
        "raw_lower_products": {},
        "inner": [{"pivot": PIVOTS[0], "positions": positions, "eligible": len(eligible)}],
    }
    pairs, digest = replay(source, fixture)
    assert pairs == 720600 and digest == DIGEST
    print(f"Paley far periodic: 2396 x 1201, 637 eligible, signed distance 483, {pairs} exact products, SHA256 {digest}")


    selected = tuple(j for j in range(SIDE) if MIXED_SOURCE_MASK >> j & 1)
    assert len(selected) == 600 and set(selected) <= set(eligible)
    assert not set(selected) & set(MIXED_PIVOTS)
    singles = [source[g] ^ (1 << r) for r,g in zip(MIXED_ROWS, MIXED_PIVOTS, strict=True)]
    assert tuple(SIDE - 2*(raw ^ z).bit_count() for z in singles) == (0,-28,-8,-12,4,-28)
    mixed = assemble(599, source, selected, [raw, *singles])
    assert len(mixed) == 1207 and verify_orthogonal(2396,mixed) == 727821
    assert sha256(b"".join(x.to_bytes(300,"little") for x in mixed)).hexdigest() == MIXED_DIGEST
    unused = [j for j in range(SIDE) if not (MIXED_SOURCE_MASK >> j & 1)]
    residues = [tuple(v[j] for j in unused)
                for v in (half_projections(source,z) for z in [raw,*singles])]
    assert rank_mod(residues,599) == 7
    print("Paley far mixed: one distance-483 inner and six single flips, 2396 x 1207, 727821 exact products")


if __name__ == "__main__":
    verify()
