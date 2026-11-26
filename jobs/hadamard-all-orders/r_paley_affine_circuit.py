"""Exact affine-circuit controls and structural dimensions for the Paley lift."""

from functools import reduce
from itertools import combinations
from operator import xor

from r_paley_full92_contrast import AGREE, OPPOSITE
from r_paley_full92_skew import build_source, frame
from r_paley_full92_unrestricted import NEXT_PIVOTS, NEXT_ROOTS, NEXT_SELECTED
from r_paley_isotropic_code import assemble, half_projections
from verify import paley, verify_orthogonal


FULL_28 = (1989, 1722, 1550, 1479, 1420, 1249, 1213, 1177, 747, 710, 675, 369)
CIRCUIT_44 = (51435, 110989, 162455, 197617)


def binary_rank(words):
    basis = {}
    for word in words:
        while word:
            pivot = word.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = word
                break
            word ^= basis[pivot]
    return len(basis)


def determinant(rows):
    """Bareiss elimination, including row exchanges and exact division."""
    matrix = [list(row) for row in rows]
    denominator = sign = 1
    for k in range(len(matrix) - 1):
        pivot_row = next((r for r in range(k, len(matrix)) if matrix[r][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            matrix[k], matrix[pivot_row] = matrix[pivot_row], matrix[k]
            sign *= -1
        pivot = matrix[k][k]
        for r in range(k + 1, len(matrix)):
            for s in range(k + 1, len(matrix)):
                numerator = pivot * matrix[r][s] - matrix[r][k] * matrix[k][s]
                matrix[r][s], remainder = divmod(numerator, denominator)
                assert remainder == 0
            matrix[r][k] = 0
        denominator = pivot
    return sign * matrix[-1][-1]


def orient(words, size):
    mask = (1 << size) - 1
    return tuple(word ^ mask if word & 1 else word for word in words)


def verify_circuit_control(t, words, complete):
    m = 2 * t - 2
    source = paley(m - 1)
    chosen = tuple(range(t + 1))
    assert verify_orthogonal(m, source) == m * (m - 1) // 2
    words = orient(words, m)
    assert len({word.bit_count() % 2 for word in words}) == 1
    assert len(words) % 2 == 0 and reduce(xor, words, 0) == 0
    assert binary_rank([word | (1 << m) for word in words]) == len(words) - 1
    for removed in range(len(words)):
        lifted = [word | (1 << m) for k, word in enumerate(words) if k != removed]
        assert binary_rank(lifted) == len(words) - 1

    top_mask = (1 << t) - 1
    balanced = []
    for word in words:
        b = half_projections(source, word)
        assert all(abs(b[j]) == 1 for j in chosen)
        epsilon = word.bit_count() % 2
        for j in chosen:
            formula = (2 - t + source[j].bit_count() + epsilon) // 2
            formula += (word.bit_count() - epsilon) // 2 + (source[j] & word).bit_count()
            assert (b[j] == -1) == bool(formula % 2)
        top = sum((b[j] == -1) << k for k, j in enumerate(chosen[1:]))
        border = (3 << (4 * t - 2)) if b[chosen[0]] == 1 else 0
        full = top | ((top ^ top_mask) << t) | ((word ^ source[chosen[0]]) << (2 * t)) | border
        assert full.bit_count() == 2 * t
        balanced.append(full)
    e = ((1 << (2 * t)) - 1) | (3 << (4 * t - 2))
    assert reduce(xor, balanced, 0) == e
    assert all((e & column).bit_count() % 2 == 1 for column in balanced)
    assert all((left & right).bit_count() == t for left, right in combinations(balanced, 2))

    matrix = assemble(t, source, chosen, words)
    assert verify_orthogonal(4 * t, matrix) == len(matrix) * (len(matrix) - 1) // 2
    if complete:
        assert len(words) == m
        signs = [[1 - 2 * (word >> r & 1) for word in words] for r in range(m)]
        assert abs(determinant(signs)) == (1 << m) * t ** ((t - 3) // 2)
        core = [[int((word ^ words[0]) >> r & 1) for word in words[1:]] for r in range(1, m)]
        abs_det = abs(determinant(core))
        assert abs_det % 4 == 2
        assert binary_rank([word ^ words[0] for word in words[1:]]) == m - 2
        mixed = 0
        for word in words:
            d = sum(((word >> r) ^ (word >> (r + 1))) & 1 for r in range(0, 10, 2))
            mixed += 0 < d < 5
        assert mixed >= 5
        print(f"Order 28: full 12-word affine circuit, normalized core determinant {abs_det}, mixed {mixed}")
    else:
        assert len(matrix) == 28 and t == 11
        old_projections = [tuple(half_projections(source, word)[j] for j in chosen) for word in words]
        possible = common = 0
        for candidate in range(0, 1 << m, 2):
            b = tuple(m // 2 - (candidate ^ source[j]).bit_count() for j in chosen)
            if not all(abs(v) == 1 for v in b):
                continue
            possible += 1
            if all(m - 2 * (candidate ^ word).bit_count() +
                   2 * sum(v * w for v, w in zip(b, old, strict=True)) == 0
                   for word, old in zip(words, old_projections, strict=True)):
                common += 1
        assert (possible, common) == (334, 0)
        print("Order 44: exact 28 columns, raw circuit size 4, 334 eligible words, none compatible with all four")


def verify_2396():
    m = 1196
    crt = [sum(1 << (block * 299 + r) for r in range(299) if r % modulus == phase)
           for block in range(4) for modulus in (13, 23) for phase in range(modulus)]
    assert binary_rank(crt) == 4 * (13 + 23 - 1) == 140
    normalization = 1
    parity = (1 << m) - 1
    equations = [((basis & normalization).bit_count() % 2) |
                 (((basis & parity).bit_count() % 2) << 1) for basis in crt]
    assert binary_rank(equations) == 2
    assert (m - 2) - (binary_rank(crt) - 2) + 1 == 1057

    pairs = []
    for r in range(m):
        block, v = divmod(r, 299)
        reflected = (v + 23 * ((4 * (12 - 2 * (v % 13))) % 13)) % 299
        s = block * 299 + reflected
        assert reflected % 23 == v % 23 and reflected % 13 == 12 - v % 13
        if r < s:
            pairs.append((r, s))
    assert len(pairs) == 552 and len({r for pair in pairs for r in pair}) == 1104

    source = build_source()
    centers, pivots = frame()
    roots = [centers[j] for j in AGREE + OPPOSITE] + list(NEXT_ROOTS)
    reserves = [pivots[j] for j in AGREE + OPPOSITE] + list(NEXT_PIVOTS)
    chosen = [j for j in range(m) if NEXT_SELECTED >> j & 1]
    words = orient([source[j] ^ (1 << r) for r, j in zip(roots, reserves, strict=True)], m)
    assert verify_orthogonal(2396, assemble(599, source, chosen, words)) == 739936
    assert binary_rank([word | (1 << m) for word in words]) == len(words) == 17
    print("Order 2396: existing 17 raw words affine independent; complete inner geometry requires 1057 nonseparable and 552 reflection-mixed words")


if __name__ == "__main__":
    verify_circuit_control(7, FULL_28, complete=True)
    verify_circuit_control(11, CIRCUIT_44, complete=False)
    verify_2396()
