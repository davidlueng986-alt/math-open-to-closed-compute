"""Exact mod-8 certificate for a defect-12 D12+ residual model at t=599."""

from collections import defaultdict
from itertools import combinations


DIMENSION = 12
TETRAHEDRON = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))


def integer_dot(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True))


def binary_dot(left, right):
    return (left & right).bit_count() % 2


def binary_word(bits):
    return sum(bit << i for i, bit in enumerate(bits))


def tetrahedral_partition(first=(0, 1, 2), signs=(1, 1, 1), flip_first=False):
    rest = sorted(set(range(DIMENSION)) - set(first))
    triples = [first, *(rest[i:i + 3] for i in range(0, len(rest), 3))]
    for triple_index, triple in enumerate(triples):
        for row_index, tetrahedral_row in enumerate(TETRAHEDRON):
            row = [0] * DIMENSION
            flip = -1 if flip_first and triple_index == row_index == 0 else 1
            multipliers = signs if triple_index == 0 else (1, 1, 1)
            for j, coordinate in enumerate(triple):
                row[coordinate] = 2 * flip * tetrahedral_row[j] * multipliers[j]
            yield tuple(row)


def doubled_shadow_frame(t):
    assert t % 2 == 1
    half_blocks = 1 if t % 4 == 3 else 3
    sparse_blocks = (t - 3 * half_blocks) // 4
    generators = [(0, 1, j) for j in range(2, DIMENSION)] + [(0, 2, 3), (1, 2, 3)]
    rows = [row for triple in generators for row in tetrahedral_partition(triple)]

    for _ in range(3 * half_blocks):
        rows.extend(tetrahedral_partition((0, 1, 2), (1, 1, 1), True))
        rows.extend(tetrahedral_partition((1, 3, 4), (-1, 1, 1), True))
        rows.extend(tetrahedral_partition((2, 3, 4), (-1, -1, -1), True))
    assert len(rows) <= 16 * sparse_blocks
    for _ in range(sparse_blocks - len(rows) // 16):
        rows.extend(tetrahedral_partition())

    squares = {i * i % 11 for i in range(1, 11)}

    def character(value):
        residue = value % 11
        return 0 if residue == 0 else (1 if residue in squares else -1)

    paley = [[1] * DIMENSION]
    paley.extend([1, *(character(j - i) - int(i == j) for j in range(11))] for i in range(11))
    for row in paley:
        row[1] *= -1
    rows.extend(tuple(row) for _ in range(half_blocks) for row in paley)
    return rows


def doubled_lattice_basis():
    """Replace e_0-e_1 by h in the D12 root basis and double the vectors."""
    basis = [(1,) * DIMENSION]
    for i in range(1, DIMENSION - 1):
        row = [0] * DIMENSION
        row[i], row[i + 1] = 2, -2
        basis.append(tuple(row))
    basis.append((0,) * (DIMENSION - 2) + (2, 2))
    return basis


def hyperbolic_basis(words, pairing, quadratic):
    """Return paired isotropic vectors for a nonsingular Arf-zero space."""
    words = list(words)
    hyperbolic = []
    anisotropic = []
    while words:
        u = words.pop()
        j = next(i for i, w in enumerate(words) if pairing(u, w))
        v = words.pop(j)
        qu, qv = quadratic(u), quadratic(v)
        if qu and qv:
            anisotropic.append((u, v))
        else:
            hyperbolic.append((u ^ v if qu else u, u ^ v if qv else v))
        for i, w in enumerate(words):
            words[i] = w ^ (u if pairing(v, w) else 0) ^ (v if pairing(u, w) else 0)

    assert len(anisotropic) % 2 == 0
    for (a, b), (c, d) in zip(anisotropic[::2], anisotropic[1::2], strict=True):
        w = a ^ b ^ d
        hyperbolic.extend(((a ^ c, b ^ c), (w, c ^ w)))
    assert all(pairing(u, v) == 1 and quadratic(u) == quadratic(v) == 0 for u, v in hyperbolic)
    return hyperbolic


def orthogonal_complement(words, n):
    """Find a basis of G-perp within the even words with coordinate 0 zero."""
    rank = len(words)
    low_mask = (1 << rank) - 1
    rows = [binary_word(binary_dot(w, v) for v in words) | (1 << (rank + i))
            for i, w in enumerate(words)]
    for j in range(rank):
        pivot = next(i for i in range(j, rank) if (rows[i] >> j) & 1)
        rows[j], rows[pivot] = rows[pivot], rows[j]
        for i in range(rank):
            if i != j and (rows[i] >> j) & 1:
                rows[i] ^= rows[j]
    assert all((row & low_mask) == (1 << i) for i, row in enumerate(rows))
    inverse = [row >> rank for row in rows]

    pivots = {}
    ones = (1 << n) - 1
    for j in range(1, n):
        v = 1 | (1 << j)
        pairings = binary_word(binary_dot(w, v) for w in words)
        for w, row in zip(words, inverse, strict=True):
            if binary_dot(pairings, row):
                v ^= w
        if v & 1:
            v ^= ones
        while v:
            bit = v.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = v
                break
            v ^= pivots[bit]
    return list(pivots.values())


def binary_sign_columns(frame, basis):
    n = len(frame)
    images = []
    for b in basis:
        reference = integer_dot(b, frame[0])
        pairings = [integer_dot(b, r) - reference for r in frame]
        assert all(value % 4 == 0 for value in pairings)
        images.append(binary_word((value // 4) % 2 for value in pairings))
    complement = orthogonal_complement(images, n)
    d = n - DIMENSION - 2
    assert len(complement) == d

    def abstract_pairing(u, v):
        return binary_dot(u, v) ^ (u.bit_count() & v.bit_count() & 1)

    def abstract_quadratic(u):
        return ((u.bit_count() + 1) // 2) % 2

    domain = hyperbolic_basis((1 << j for j in range(d)), abstract_pairing, abstract_quadratic)
    target = hyperbolic_basis(complement, binary_dot, lambda u: (u.bit_count() // 2) % 2)
    simplex = []
    final = 0
    for j in range(d):
        coordinate = 1 << j
        y = 0
        for (a, b), (u, v) in zip(domain, target, strict=True):
            if abstract_pairing(coordinate, b):
                y ^= u
            if abstract_pairing(coordinate, a):
                y ^= v
        simplex.append(y)
        final ^= y
    simplex.append(final)
    row_parity = binary_word(row[0] % 2 for row in frame)
    return [0, *(y ^ row_parity for y in simplex)]


def verify(t=599):
    n = 4 * t
    frame = doubled_shadow_frame(t)
    assert len(frame) == n
    assert all(integer_dot(r, r) == DIMENSION for r in frame)
    assert all(sum(r) % 4 == 2 and len({value % 2 for value in r}) == 1 for r in frame)
    assert {r[0] % 2 for r in frame} == {0, 1}
    coordinates = list(zip(*frame, strict=True))
    for i, coordinate in enumerate(coordinates):
        assert sum(coordinate) == 0
        assert all(integer_dot(coordinate, other) == n * int(i == j)
                   for j, other in enumerate(coordinates))

    basis = doubled_lattice_basis()
    columns = binary_sign_columns(frame, basis)
    assert len(columns) == n - DIMENSION
    assert all(x % 2 == 0 for x in columns)
    assert all((x ^ y).bit_count() % 4 == 2 for x, y in combinations(columns, 2))

    # The i-th sign entry is (-1)^(column bit i). Verify C^T A mod 8
    # directly, where C_i is the list of inner products 2 <rho_i,b>.
    for b in basis:
        masks = defaultdict(int)
        for i, r in enumerate(frame):
            pair = integer_dot(b, r)
            assert pair % 2 == 0
            masks[(pair // 2) % 4] |= 1 << i
        assert all(sum(value * (mask & x).bit_count() for value, mask in masks.items()) % 4 == 0
                   for x in columns)

    sign_rows = [binary_word((x >> i) & 1 for x in columns) for i in range(n)]
    assert all(row.bit_count() % 2 == r[0] % 2 for row, r in zip(sign_rows, frame, strict=True))
    shifts = {(r, s): (n - DIMENSION + integer_dot(r, s)) % 8
              for r in set(frame) for s in set(frame)}
    for i, (row, residual) in enumerate(zip(sign_rows, frame, strict=True)):
        for j in range(i):
            assert 2 * (row ^ sign_rows[j]).bit_count() % 8 == shifts[residual, frame[j]]

    print(f"n={n}: exact zero-sum D12+ shadow frame, both Gram identities modulo 8")


if __name__ == "__main__":
    verify()
