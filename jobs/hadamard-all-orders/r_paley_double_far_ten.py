"""Replay a two-far, ten-single Paley extension at order 2396."""

from collections import Counter
from hashlib import sha256
from itertools import combinations

from r_paley_double_far import build_source, dot, fibres
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from verify import rows_from_columns, verify_orthogonal


ROWS = (574, 361, 764, 896, 772, 514, 299, 739, 730, 720)
BEFORE_PIVOTS = (786, 96, 1010, 645, 320, 854, 391, 498, 1110, 515)
PIVOTS = (786, 434, 1010, 645, 320, 854, 391, 656, 654, 515)
BEFORE_SELECTED = int(
    "bdffebff57f0ffdfda3ff3d7ad6ded2ffe7bf3ffc5de8bb7fe3ff1f34ff76b33"
    "ff9ffeffb6f401a00d010800405a02d01480b404802d01680b00520290168034"
    "04a02901680b405a02901680b405002c01080a005a02c016803400a02c01680a"
    "005a025016809005a00d016809405a02bef9737f3fbdfbebbf7debefdff0dd77"
    "f3a3fddfeff76be3efcfbeefb7eeade9fbee7f7ff38",
    16,
)
SELECTED = int(
    "bdffebbb57b9ffddda3ff38fad6dfcafff7ffbfb56de5fb7ffbfedf2eff76b3b"
    "ff9eaefff6f401a024010808404a02c01480b405a02901680b005a02c0168030"
    "04a02901680340520090128014058029016808005a02d016803404a02d01680a"
    "405a02d016809005a00d006809405a027cfd33ed36fdfbc3f57fdbbfdff25d77"
    "f7bbfd9fedf54bf3fdd5fceff3ffbde9fbee7f5fe3a",
    16,
)
DIGEST = "c17b655963d1417f213b9a35ae4a09be552d366c18fff3d2c6be1aefcbe99969"


def sign(word, i):
    return 2 * (word >> i & 1) - 1


def alternate_pair(source):
    groups = fibres()
    words = []
    for index in (45, 6):
        col = source[groups[index][0]]
        word = 0
        for group in groups:
            total = sum(sign(col, r) for r in group)
            assert total % 2
            if total > 0:
                word |= sum(1 << r for r in group)
        words.append(word if word & 1 else word ^ ((1 << len(source)) - 1))
    return words


def requirement_errors(source, far, profiles, selected, pivots):
    q = [half_projections(source, word) for word in far]
    directions = [sign(source[g], r) for r, g in zip(ROWS, pivots, strict=True)]
    errors = {}
    for (i, r), (j, s) in combinations(enumerate(ROWS), 2):
        actual = sum(profiles[i][h] * profiles[j][h] for h in selected)
        required = directions[i] * sign(source[pivots[i]], s)
        required += directions[j] * sign(source[pivots[j]], r)
        if actual != required:
            errors[i, j] = actual - required
    for a, deck in enumerate(q):
        for i, r in enumerate(ROWS):
            actual = -sum(deck[j] * profiles[i][j] for j in selected)
            required = sign(far[a], r) - directions[i] * deck[pivots[i]]
            assert actual == required
    return errors


def verify():
    source = build_source()
    assert verify_orthogonal(1196, source) == 714610
    far = alternate_pair(source)
    q = [half_projections(source, word) for word in far]
    assert dot(*far) == 0
    assert all(max(map(abs, deck)) == 115 for deck in q)
    assert all(min((1196 - abs(2 * v)) // 2 for v in deck) == 483 for deck in q)
    assert all(sum(abs(v) == 1 for v in deck) == 759 for deck in q)
    joint = [j for j, (a, b) in enumerate(zip(*q, strict=True)) if abs(a) == abs(b) == 1]
    assert len(joint) == 736 and sum(q[0][j] == q[1][j] for j in joint) == 368
    chosen = [j for j in range(1196) if SELECTED >> j & 1]
    before = [j for j in range(1196) if BEFORE_SELECTED >> j & 1]
    for selection, reserves in ((chosen, PIVOTS), (before, BEFORE_PIVOTS)):
        assert len(selection) == 600 and set(selection).issubset(joint)
        assert sum(q[0][j] == q[1][j] for j in selection) == 300
        assert len(set(reserves)) == len(set(ROWS)) == 10
        assert set(reserves).isdisjoint(selection)
    assert len(set(chosen) - set(before)) == 57
    unchanged = [i for i in range(len(ROWS)) if BEFORE_PIVOTS[i] == PIVOTS[i]]
    assert unchanged == [0, 2, 3, 4, 5, 6, 9]
    profiles = [[sign(col, r) for col in source] for r in ROWS]
    preserved = [q[0], q[1], *(profiles[i] for i in unchanged)]

    def signature(j):
        return tuple(p[j] == q[0][j] for p in preserved[1:])

    assert Counter(map(signature, before)) == Counter(map(signature, chosen))
    before_errors = requirement_errors(source, far, profiles, before, BEFORE_PIVOTS)
    assert set(before_errors) == {(0, 7), (1, 3), (6, 8)}
    assert all(abs(delta) == 2 for delta in before_errors.values())
    assert not requirement_errors(source, far, profiles, chosen, PIVOTS)
    singles = [source[g] ^ (1 << r) for r, g in zip(ROWS, PIVOTS, strict=True)]
    words = far + singles
    columns = assemble(599, source, chosen, words)
    assert len(columns) == 1212 and verify_orthogonal(2396, columns) == 733866
    points = (1 << 2394) - 1
    outside = [col & points for col in columns[:1198]]
    blocks = rows_from_columns(2394, outside)
    assert len(set(blocks)) == 2394 and all(block.bit_count() == 599 for block in blocks)
    assert all((a & b).bit_count() == 598 for a, b in combinations(outside, 2))
    unused = sorted(set(range(1196)) - set(chosen))
    reserves = [tuple(deck[j] for j in unused) for deck in
                (half_projections(source, word) for word in words)]
    assert rank_mod(reserves, 599) == 12
    digest = sha256(b"".join(col.to_bytes(300, "little") for col in columns)).hexdigest()
    assert digest == DIGEST
    print("Paley double far: 2396 x 1212, two signed distances 483, ten one-flips, 733866 zero products")
    print("Seven preserved row profiles, three changed pivots, 57 reselected columns, reserve rank 12")
    print("SHA256", digest)


if __name__ == "__main__":
    verify()
