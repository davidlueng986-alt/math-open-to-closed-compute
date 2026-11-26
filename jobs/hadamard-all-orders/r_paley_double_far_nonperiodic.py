"""Replay a nonperiodic far pair using a different physical T23 selector."""

from hashlib import sha256

from r_paley_double_far import BLOCK, ORDER, SIDE, WILLIAMSON, build_source as periodic_source, dot, fibres
from r_paley_far_family import quaternion_basis
from r_paley_isotropic_code import assemble, half_projections, rank_mod
from verify import goethals_seidel, signs, verify_orthogonal


BASE_MASKS = (41, 2513, 1159, 1239)
BASE_LENGTHS = (12, 12, 11, 11)
UNIT_PERMUTATION = (2, 1, 0, 3)
TARGET_SUMS = (1, -3, -3, -2)
PIVOTS = (32, 19)
FLIP_ROWS = (903, 1046)
DIGEST = "c2ed77155418767db831e7d3c203d426973a848b3e2faba52246fef6b6f5cd53"


def selector():
    base = [tuple(2 * ((mask >> j) & 1) - 1 for j in range(length))
            for mask, length in zip(BASE_MASKS, BASE_LENGTHS, strict=True)]
    assert all(sum(word[i] * word[i + shift] for word in base
                   for i in range(len(word) - shift)) == 0 for shift in range(1, 12))
    entries = [(2 * side + int(a != b), a) for side in range(2)
               for a, b in zip(*base[2 * side:2 * side + 2], strict=True)]
    sums = [sum(v for k, v in entries if k == u) for u in range(4)]
    assert all(abs(sums[u]) == abs(TARGET_SUMS[k]) for u, k in enumerate(UNIT_PERMUTATION))
    normalized = tuple((UNIT_PERMUTATION[u], v * TARGET_SUMS[UNIT_PERMUTATION[u]] // sums[u])
                       for u, v in entries)
    assert tuple(sum(v for k, v in normalized if k == u) for u in range(4)) == TARGET_SUMS
    assert all(sum(s * t for (i, s), (j, t) in zip(normalized, normalized[shift:]) if i == j) == 0
               for shift in range(1, len(normalized)))
    return normalized


def build_source():
    base = tuple(map(signs, WILLIAMSON))
    choose = selector()
    units = [quaternion_basis(*row) for row in zip(*base, strict=True)]
    words = [[s * units[i % len(units)][u][j] for i in range(BLOCK)
              for u, s in (choose[i % len(choose)],)] for j in range(4)]
    assert all(sum(word[i] * word[(i + shift) % BLOCK] for word in words
                   for i in range(BLOCK)) == 0 for shift in range(1, BLOCK))
    return goethals_seidel(words)


def raw_pair(source):
    groups = fibres()
    raw = []
    for p in PIVOTS:
        mask = source[groups[p][0]]
        word = sum(1 << r for group in groups
                   if sum(2 * ((mask >> i) & 1) - 1 for i in group) > 0 for r in group)
        raw.append(word if word & 1 else word ^ ((1 << SIDE) - 1))
    assert dot(*raw) == 0
    assert all(r in groups[45] for r in FLIP_ROWS)
    return raw[0] ^ sum(1 << r for r in FLIP_ROWS), raw[1]


def verify():
    source = build_source()
    reference = periodic_source()
    assert len(source) == SIDE and source != reference
    assert verify_orthogonal(SIDE, source) == 714610
    fiber_masks = [sum(1 << r for r in group) for group in fibres()]
    assert all((c & mask).bit_count() == (d & mask).bit_count()
               for c, d in zip(source, reference, strict=True) for mask in fiber_masks)

    x, y = raw_pair(source)
    assert dot(x, y) == -4
    assert sum(min(a, 23 - a) for a in ((x & mask).bit_count() for mask in fiber_masks)) == 2
    assert all((y & mask).bit_count() in (0, 23) for mask in fiber_masks)
    decks = tuple(tuple(dot(w, c) for c in source) for w in (x, y))
    distance = tuple((SIDE - max(map(abs, deck))) // 2 for deck in decks)
    assert distance == (481, 483)
    same = [j for j, (a, b) in enumerate(zip(*decks, strict=True)) if abs(a) == 2 and a == b]
    opposite = [j for j, (a, b) in enumerate(zip(*decks, strict=True)) if abs(a) == 2 and a == -b]
    assert (len(same), len(opposite)) == (316, 300)
    needed = (300 - dot(x, y) // 4, 300 + dot(x, y) // 4)
    assert needed == (301, 299)
    selected = sorted(same[:needed[0]] + opposite[:needed[1]])
    assert len(selected) == 600
    matrix = assemble(599, source, selected, (x, y))
    assert len(matrix) == 1202 and verify_orthogonal(ORDER, matrix) == 721801
    reserve = sorted(set(range(SIDE)) - set(selected))
    code = [tuple(values[j] for j in reserve) for values in (half_projections(source, z) for z in (x, y))]
    assert rank_mod(code, 599) == 2
    digest = sha256(b"".join(column.to_bytes(300, "little") for column in matrix)).hexdigest()
    assert digest == DIGEST
    print("Nonperiodic far pair: distances 481 and 483, available 316 + 300, selected 301 + 299")
    print("2396 x 1202; all 721801 column products zero; reserve rank 2")
    print("SHA256", digest)


if __name__ == "__main__":
    verify()
