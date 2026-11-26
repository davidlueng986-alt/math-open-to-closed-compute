"""Rebuild two jointly compatible far words using a T23 × Williamson13 source."""

from hashlib import sha256
from itertools import combinations

from r_paley_far_family import quaternion_basis
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from verify import goethals_seidel, rows_from_columns, signs, verify_orthogonal

BLOCK = 299
SIDE = 1196
ORDER = 2396
PERIOD = 13
WILLIAMSON = (
    "+-++------++-",
    "+-++------++-",
    "++---+--+---+",
    "+-+++-++-+++-",
)
SELECTOR = (
    (1, 1), (1, -1), (1, 1), (1, -1), (2, 1), (2, -1),
    (2, -1), (2, -1), (1, -1), (1, -1), (1, -1), (2, -1),
    (3, -1), (0, 1), (3, -1), (3, -1), (3, 1), (0, -1),
    (3, -1), (3, 1), (3, 1), (0, 1), (3, -1),
)
PIVOTS = (32, 19)
DIGEST = "8b4a64e9772434dd64bea065581c0c1b063abeee566435674d20bcec45296fc7"


def build_source():
    base = tuple(map(signs, WILLIAMSON))
    assert all(len(word) == PERIOD and word[r] == word[-r % PERIOD]
               for word in base for r in range(PERIOD))
    assert all(sum(word[r] * word[(r + d) % PERIOD]
                   for word in base for r in range(PERIOD)) == 0 for d in range(1, PERIOD))
    assert len(SELECTOR) == 23
    assert tuple(sum(v for k, v in SELECTOR if k == j) for j in range(4)) == (1, -3, -3, -2)
    assert all(sum(v * w for (a, v), (b, w) in zip(SELECTOR, SELECTOR[d:]) if a == b) == 0
               for d in range(1, len(SELECTOR)))
    units = [quaternion_basis(*row) for row in zip(*base)]
    words = [[] for _ in range(4)]
    for r in range(BLOCK):
        unit, sign = SELECTOR[r % 23]
        for row, value in zip(words, units[r % PERIOD][unit], strict=True):
            row.append(sign * value)
    assert all(sum(word[r] * word[(r + d) % BLOCK]
                   for word in words for r in range(BLOCK)) == 0 for d in range(1, BLOCK))
    return goethals_seidel(words)


def fibres():
    return tuple(tuple(b * BLOCK + r for r in range(s, BLOCK, PERIOD))
                 for b in range(4) for s in range(PERIOD))


def dot(left, right, size=SIDE):
    return size - 2 * (left ^ right).bit_count()


def build_pair(source):
    groups = fibres()
    assert len(groups) == 52 and all(len(g) == 23 for g in groups)
    result = []
    decks = []
    for pivot in PIVOTS:
        source_col = source[groups[pivot][0]]
        support = []
        for row in groups:
            value = sum(2 * (source_col >> r & 1) - 1 for r in row)
            assert value % 2
            if value > 0:
                support.extend(row)
        raw = sum(1 << r for r in support)
        if not raw & 1:
            raw ^= (1 << SIDE) - 1
        deck = tuple(dot(raw, col) for col in source)
        assert all(deck[j] == deck[g[0]] for g in groups for j in g)
        assert sum(abs(v) == 2 for v in deck) == 759
        assert max(map(abs, deck)) == 230
        assert min((SIDE - abs(v)) // 2 for v in deck) == 483
        result.append(raw)
        decks.append(deck)
    assert dot(*result) == 0
    same = [j for j, (a, b) in enumerate(zip(*decks, strict=True)) if abs(a) == 2 and a == b]
    opp = [j for j, (a, b) in enumerate(zip(*decks, strict=True)) if abs(a) == 2 and a == -b]
    assert len(same) == len(opp) == 368
    chosen = sorted(same[:300] + opp[:300])
    assert len(chosen) == len(set(chosen)) == 600
    return result, chosen


def verify():
    source = build_source()
    assert len(source) == SIDE and verify_orthogonal(SIDE, source) == 714610
    raw, chosen = build_pair(source)
    witness = assemble(599, source, chosen, raw)
    assert len(witness) == 1202
    pairs = verify_orthogonal(ORDER, witness)
    assert pairs == 721801
    point_mask = (1 << (ORDER - 2)) - 1
    outside = [col & point_mask for col in witness[:1198]]
    blocks = rows_from_columns(ORDER - 2, outside)
    assert len(set(blocks)) == ORDER - 2 and all(row.bit_count() == 599 for row in blocks)
    assert all((a & b).bit_count() == 598 for a, b in combinations(outside, 2))
    unused = sorted(set(range(SIDE)) - set(chosen))
    code = [tuple(p[j] for j in unused) for p in (half_projections(source, z) for z in raw)]
    assert rank_mod(code, 599) == 2
    digest = sha256(b"".join(c.to_bytes(300, "little") for c in witness)).hexdigest()
    assert digest == DIGEST
    print("Paley double far: 2396 x 1202, both signed distances 483, "
          "368 same and 368 opposite eligible, all 721801 column products zero")
    print("SHA256", digest)


if __name__ == "__main__":
    verify()
