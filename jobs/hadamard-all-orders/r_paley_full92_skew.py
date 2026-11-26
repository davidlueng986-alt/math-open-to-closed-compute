"""Verify a full 92-row skew reserve frame in an order-1196 Hadamard source."""

from collections import Counter
from hashlib import sha256
from itertools import combinations
from math import comb

from r_paley_double_far import WILLIAMSON
from r_paley_far_family import quaternion_basis
from r_paley_periodic_skew import check_frame, coordinate, sign
from verify import goethals_seidel, signs, verify_orthogonal


SELECTOR = (
    (2, 1), (1, -1), (2, -1), (2, 1), (2, -1), (1, -1),
    (1, 1), (2, -1), (2, -1), (2, -1), (1, -1), (1, -1),
    (3, 1), (3, -1), (0, 1), (0, -1), (3, 1), (0, -1),
    (3, -1), (0, 1), (0, 1), (3, -1), (3, -1),
)
WORD_ORDER = (2, 0, 1, 3)
OFFSET = 9
SOURCE_DIGEST = "1c869717db8f05c656c012e714a15ddc601f33c560e8f2acbc43fe787d2ea17c"


def build_source():
    """Use a complementary selector and a permuted quaternion output."""
    williamson = tuple(map(signs, WILLIAMSON))
    assert all(word[r] == word[-r % 13] for word in williamson for r in range(13))
    assert all(sum(word[r] * word[(r + d) % 13]
                   for word in williamson for r in range(13)) == 0 for d in range(1, 13))
    assert len(SELECTOR) == 23
    assert tuple(sum(s for u, s in SELECTOR if u == a) for a in range(4)) == (1, -3, -3, -2)
    assert all(sum(s*t for (a, s), (b, t) in zip(SELECTOR, SELECTOR[d:]) if a == b) == 0
               for d in range(1, 23))
    units = [quaternion_basis(*w) for w in zip(*williamson, strict=True)]
    words = [[s * units[r % 13][u][j] for r in range(299)
              for u, s in (SELECTOR[r % 23],)] for j in WORD_ORDER]
    assert all(sum(w[r] * w[(r + d) % 299] for w in words for r in range(299)) == 0
               for d in range(1, 299))
    assert units[0][0] == (1, 1, 1, 1)
    diagonal_word = [s * units[0][u][WORD_ORDER[0]] for u, s in SELECTOR]
    assert all(diagonal_word[(OFFSET + j) % 23] == -diagonal_word[(OFFSET - j) % 23]
               for j in range(1, 23))
    assert words[0][78] == diagonal_word[OFFSET]
    return goethals_seidel(words)


def frame():
    rows = [coordinate(b, 6, t) for b in range(4) for t in range(23)]
    pivots = [coordinate(b, 6, (t + OFFSET) % 23) for b in range(4) for t in range(23)]
    return rows, pivots


def verify():
    source = build_source()
    assert len(source) == 1196
    assert verify_orthogonal(1196, source) == 714610
    digest = sha256(b"".join(col.to_bytes(150, "little") for col in source)).hexdigest()
    assert digest == SOURCE_DIGEST
    rows, pivots = frame()
    assert len(rows) == len(pivots) == 92 and set(rows) == set(pivots)
    assert all((g % 299 - r % 299) % 299 == 78 for r, g in zip(rows, pivots, strict=True))
    assert len({sign(source[g], r) for r, g in zip(rows, pivots, strict=True)}) == 1
    check_frame(source, rows, pivots)
    assert comb(len(rows), 2) == 4186
    local_mask = (1 << 92) - 1
    decks = Counter()
    central_deck = None
    for residue in range(13):
        fibre = [source[coordinate(b, residue, t)] for b in range(4) for t in range(23)]
        local = [sum((column >> r & 1) << i for i, r in enumerate(rows)) for column in fibre]
        assert verify_orthogonal(92, local) == 4186
        deck = tuple(sorted(v if v & 1 else v ^ local_mask for v in local))
        decks[deck] += 1
        if residue == 6:
            central_deck = deck
    assert sorted(decks.values()) == [1, 4, 8]
    assert decks[central_deck] == 1
    assert len(set().union(*map(set, decks))) == 276
    print("H1196 source: 714610 pair products, SHA256", digest)
    print("Full 92-row frame: 4186 skew contacts, all", comb(92, 16), "16-row subsets skew")
    print("13 local H92 fibres: 54418 pair products, three disjoint decks of multiplicities 1/4/8")


if __name__ == "__main__":
    verify()
