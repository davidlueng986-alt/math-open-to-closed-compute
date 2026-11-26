"""Replay an alternative T13 source with eight explicit periodic far words."""

from hashlib import sha256
from itertools import combinations

from r_paley_far_family import product_words, quaternion_basis
from r_paley_far_periodic import row_fibres
from r_paley_isotropic_code import assemble
from verify import goethals_seidel, length_299_words, verify_orthogonal


SELECTOR = (
    (1,1), (1,-1), (0,1), (0,-1), (0,-1), (1,-1), (0,-1),
    (3,-1), (2,-1), (2,1), (2,1), (2,1), (3,-1),
)
COMPRESSED_PIVOTS = (4,18,27,41,50,64,73,87)
DIGEST = "e0f36e2532881706a25ce5c5a9df04d14c41ee594aee751b7a73cd7745d95f2e"


def verify():
    assert [sum(s for unit,s in SELECTOR if unit == i) for i in range(4)] == [-2,-1,2,-2]
    for shift in range(1,13):
        assert sum(SELECTOR[i][1]*SELECTOR[i+shift][1]
                   for i in range(13-shift) if SELECTOR[i][0] == SELECTOR[i+shift][0]) == 0

    baseline = length_299_words()
    units = [quaternion_basis(*(word[13*(16*y % 23)] for word in baseline)) for y in range(23)]
    source = goethals_seidel(product_words(SELECTOR, units))
    assert verify_orthogonal(1196, source) == 714610
    fibres = row_fibres()
    far = {}
    for seed, cols in enumerate(fibres):
        column = source[cols[0]]
        means = [2*sum(column >> r & 1 for r in rows)-13 for rows in fibres]
        raw = sum(1 << r for rows,a in zip(fibres,means,strict=True) if a > 0 for r in rows)
        if not (raw & 1):
            raw ^= (1 << 1196)-1
        deck = [1196-2*(raw ^ h).bit_count() for h in source]
        eligible = {j for j,a in enumerate(deck) if abs(a) == 2}
        if len(eligible) >= 600:
            distance = (1196-max(map(abs,deck)))//2
            assert (len(eligible),distance) == (624,439)
            far[seed] = raw, eligible
    assert tuple(far) == COMPRESSED_PIVOTS and len({z for z,_ in far.values()}) == 8
    assert max(len(e & f) for (_,e),(_,f) in combinations(far.values(),2)) == 403
    z,e = far[73]
    cols = assemble(599,source,sorted(e)[:600],[z])
    assert len(cols) == 1201 and verify_orthogonal(2396,cols) == 720600
    assert sha256(b"".join(c.to_bytes(300,"little") for c in cols)).hexdigest() == DIGEST
    print("Alternative H1196: eight explicit far lines, each distance439 and 624 eligible")
    print("Alternative far witness: 2396 x 1201, all 720600 pair products zero; eight-line common capacity at most 403")


if __name__ == "__main__":
    verify()
