"""Rebuild a Cooper--Wallis H(1196) with two compatible far lower words."""

from hashlib import sha256
from itertools import combinations

from r_paley_far_alternative import SELECTOR
from r_paley_isotropic_code import assemble, half_projections
from verify import signs, verify_orthogonal


T_LEN, W_LEN = 13, 23
HEIGHT = 4 * T_LEN * W_LEN
WILLIAMSON = (
    "++---+---+-++-+---+---+",
    "+-++-++--++++++--++-++-",
    "+++---++-+-++-+-++---++",
    "+++-+++-+------+-+++-++",
)
COEFFICIENTS = (
    ((0, 1), (1, 1), (2, 1), (3, 1)),
    ((1, 1), (0, -1), (3, 1), (2, -1)),
    ((2, 1), (3, -1), (0, -1), (1, 1)),
    ((3, 1), (2, 1), (1, -1), (0, -1)),
)
BLOCKS = (
    ((0, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 1)),
    ((1, -1, 1), (0, 1, 0), (3, -1, 2), (2, 1, 2)),
    ((2, -1, 1), (3, 1, 2), (0, 1, 0), (1, -1, 2)),
    ((3, -1, 1), (2, -1, 2), (1, 1, 2), (0, 1, 0)),
)
COMPRESSED_LOWER = (0x22FD107294E64C0C93BA5DC, 0x3F36B7A5DC76FD10456B1B1)
SOURCE_DIGEST = "41165d66e8cf62fe497c85311189b48a0efef61e640a5814d2396fc3f9ec7662"
MATRIX_DIGEST = "3feea024e76c23bf87530d5788716ac38472f36e9ff5c3dfa37738aaeeb481ea"


def short_factor():
    """Four signed, disjoint Goethals--Seidel support matrices."""
    words = tuple(tuple(sign if a == active else 0 for active, sign in SELECTOR) for a in range(4))
    assert len(SELECTOR) == T_LEN
    assert all(sum(word[i] * word[(i + d) % T_LEN] for word in words for i in range(T_LEN)) == 0
               for d in range(1, T_LEN))
    width = 4 * T_LEN
    factors = []
    for deck in COEFFICIENTS:
        factor = [[0] * width for _ in range(width)]
        for br in range(4):
            for bc in range(4):
                index, sign, kind = BLOCKS[br][bc]
                u, code_sign = deck[index]
                for r in range(T_LEN):
                    for c in range(T_LEN):
                        shifts = (c - r, -1 - c - r, 1 + c + r)
                        factor[br * T_LEN + r][bc * T_LEN + c] = sign * code_sign * words[u][shifts[kind] % T_LEN]
        factors.append(factor)
    assert all(sum(abs(factor[r][c]) for factor in factors) == 1
               for r in range(width) for c in range(width))
    for factor in factors:
        assert all(sum(a * b for a, b in zip(factor[r], factor[s], strict=True)) == (T_LEN if r == s else 0)
                   for r in range(width) for s in range(width))
    for left, right in combinations(factors, 2):
        assert all(sum(a * b + c * d for a, b, c, d in zip(left[r], right[s], right[r], left[s], strict=True)) == 0
                   for r in range(width) for s in range(width))
    return factors


def build_source():
    """Take the tensor sum, with row/column order (block, short phase, long phase)."""
    long = tuple(map(signs, WILLIAMSON))
    assert all(len(word) == W_LEN and word[j] == word[-j % W_LEN] for word in long for j in range(W_LEN))
    assert all(sum(word[i] * word[(i + d) % W_LEN] for word in long for i in range(W_LEN)) == 0
               for d in range(1, W_LEN))
    factors = short_factor()
    width = 4 * T_LEN
    columns = []
    for c in range(width):
        for y in range(W_LEN):
            column = 0
            for r in range(width):
                k = next(i for i, block in enumerate(factors) if block[r][c])
                sign = factors[k][r][c]
                for x in range(W_LEN):
                    column |= ((sign * long[k][(y - x) % W_LEN]) < 0) << (r * W_LEN + x)
            columns.append(column)
    return columns


def rotate_long(word):
    mask = (1 << W_LEN) - 1
    rotated = 0
    for base in range(0, HEIGHT, W_LEN):
        part = word >> base & mask
        rotated |= (((part << 1) & mask) | (part >> (W_LEN - 1))) << base
    return rotated


def lift(word):
    mask = (1 << W_LEN) - 1
    expanded = 0
    for b in range(4):
        part = word >> (b * W_LEN) & mask
        for k in range(T_LEN):
            expanded |= part << ((b * T_LEN + k) * W_LEN)
    return expanded


def build_pair(source):
    raw = tuple(map(lift, COMPRESSED_LOWER))
    assert (raw[0] ^ raw[1]).bit_count() == HEIGHT // 2
    first, second = (half_projections(source, word) for word in raw)
    sectors = [[j for j, (a, b) in enumerate(zip(first, second, strict=True)) if abs(a) == 1 and a == sign * b]
               for sign in (1, -1)]
    counts = tuple(map(len, sectors))
    distances = tuple(HEIGHT // 2 - max(map(abs, deck)) for deck in (first, second))
    assert counts == (351, 351) and distances == (503, 503)
    selected = sorted(sectors[0][:300] + sectors[1][:300])
    assert len(selected) == len(set(selected)) == 600
    return raw, selected


def verify():
    source = build_source()
    assert verify_orthogonal(HEIGHT, source) == 714610
    assert sha256(b"".join(column.to_bytes(150, "little") for column in source)).hexdigest() == SOURCE_DIGEST
    assert all(rotate_long(source[k]) == source[(k // W_LEN) * W_LEN + (k + 1) % W_LEN]
               for k in range(HEIGHT))
    raw, selected = build_pair(source)
    columns = assemble(599, source, selected, raw)
    assert len(columns) == 1202 and verify_orthogonal(2396, columns) == 721801
    assert sha256(b"".join(column.to_bytes(300, "little") for column in columns)).hexdigest() == MATRIX_DIGEST
    print(f"Cooper--Wallis H1196: 714610 exact pairs, cyclic automorphism of order 23, SHA256 {SOURCE_DIGEST}")
    print(f"2396 x 1202: 721801 exact pairs, two signed distances 503, common 351 + 351, SHA256 {MATRIX_DIGEST}")


if __name__ == "__main__":
    verify()
