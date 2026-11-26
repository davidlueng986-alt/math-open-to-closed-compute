"""Exact H324 via Paley block product of order 108 and T3."""
from hashlib import sha256
from verify import require, verify_orthogonal

Q = 107
SIDE = 27
Z = (31, 18)


def field_mul(u, v):
    a, b = u
    c, d = v
    return (a * c - b * d) % Q, (a * d + b * c) % Q


def projective(u):
    a, b = u
    return b * pow(a, -1, Q) % Q if a else Q


def representatives():
    """One consistent vector lift of all four order-27 projective cycles."""
    require(sum(v * v for v in Z) % Q == 1, "multiplier norm")
    seen = set()
    vectors = []
    for label in range(Q + 1):
        if label in seen:
            continue
        first = (1, label) if label < Q else (0, 1)
        cycle = []
        u = first
        for _ in range(SIDE):
            node = projective(u)
            require(node not in seen, "projective cycle overlap")
            seen.add(node)
            cycle.append(u)
            u = field_mul(Z, u)
        require(u == first, "projective vector cycle length")
        vectors.extend(cycle)
    require(len(vectors) == Q + 1 == 4 * SIDE, "projective point coverage")
    return vectors


def chi(x):
    x %= Q
    if x == 0:
        return 0
    return 1 if pow(x, (Q - 1) // 2, Q) == 1 else -1


def build_paley():
    vectors = representatives()
    return [
        [
            1 if i == j else chi(a * d - b * c)
            for j, (c, d) in enumerate(vectors)
        ]
        for i, (a, b) in enumerate(vectors)
    ]


def check_rows(matrix):
    n = len(matrix)
    require(all(len(row) == n and all(value in (-1, 1) for value in row) for row in matrix),
            "square sign matrix")
    masks = [sum((value == -1) << j for j, value in enumerate(row)) for row in matrix]
    return verify_orthogonal(n, masks)


def product_sequences(paley):
    blocks = [
        [paley[i * SIDE][j * SIDE : (j + 1) * SIDE] for j in range(4)]
        for i in range(4)
    ]
    for i in range(4):
        for j in range(4):
            for x in range(SIDE):
                for y in range(SIDE):
                    require(paley[i * SIDE + x][j * SIDE + y] == blocks[i][j][(y - x) % SIDE],
                            "circulant block")
    return [[blocks[i][j] for i in range(3)] for j in range(4)]


def group_shift(s, r, ds=0, dr=0):
    return (s + ds) % 3, (r + dr) % SIDE


def product_hadamard(sequences):
    group = [(s, r) for s in range(3) for r in range(SIDE)]
    for ds, dr in group:
        correlation = 0
        for word in sequences:
            for s, r in group:
                ts, tr = group_shift(s, r, ds, dr)
                correlation += word[s][r] * word[ts][tr]
        require(correlation == (12 * SIDE if ds == dr == 0 else 0),
                f"product autocorrelation at {(ds, dr)}")
    # Goethals-Seidel, with R sending g to -g.
    blocks = (
        ((0, 1, 'D'), (1, 1, 'R'), (2, 1, 'R'), (3, 1, 'R')),
        ((1, -1, 'R'), (0, 1, 'D'), (3, 1, 'T'), (2, -1, 'T')),
        ((2, -1, 'R'), (3, -1, 'T'), (0, 1, 'D'), (1, 1, 'T')),
        ((3, -1, 'R'), (2, 1, 'T'), (1, -1, 'T'), (0, 1, 'D')),
    )
    matrix = []
    for block_row in blocks:
        for s, r in group:
            row = []
            for seq, sign, kind in block_row:
                for t, u in group:
                    if kind == 'D':
                        ds, dr = t - s, u - r
                    elif kind == 'R':
                        ds, dr = -t - s, -u - r
                    else:
                        ds, dr = t + s, u + r
                    row.append(sign * sequences[seq][ds % 3][dr % SIDE])
            matrix.append(row)
    return matrix


def main():
    p = build_paley()
    print(f"Paley H108: {check_rows(p):,} exact row inner products")
    sequences = product_sequences(p)
    matrix = product_hadamard(sequences)
    print(f"Product H324: {check_rows(matrix):,} exact row inner products")
    csv = ''.join(','.join(map(str, row)) + '\n' for row in matrix).encode()
    digest = sha256(csv).hexdigest()
    require(digest == "326a3f95e6f6402d975ad67742a936d5df5d09de113e6695ff89c76914d5541e", "H324 digest")
    print(f"H324 canonical CSV SHA-256: {digest}")


if __name__ == '__main__':
    main()
