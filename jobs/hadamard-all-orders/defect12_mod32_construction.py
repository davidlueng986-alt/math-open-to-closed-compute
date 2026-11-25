"""Direct mod-32 certificates and affine checks for the Eliahou 16k+3 family."""

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations

# Source sequence, column-index sign, row-index sign, matrix entry sign.
BLOCKS = (((0, 1, -1, 1), (1, -1, -1, -1), (2, -1, -1, -1), (3, -1, -1, -1)),
          ((1, -1, -1, 1), (0, 1, -1, 1), (3, 1, 1, -1), (2, 1, 1, 1)),
          ((2, -1, -1, 1), (3, 1, 1, 1), (0, 1, -1, 1), (1, 1, 1, -1)),
          ((3, -1, -1, 1), (2, 1, 1, -1), (1, 1, 1, 1), (0, 1, -1, 1)))


def decode(runs):
    return tuple(1 - 2 * (i % 2) for i, length in enumerate(runs) for _ in range(length))


def half_flip(s):
    h = (len(s) + 1) // 2
    return s[:h] + tuple(-x for x in s[h:])


def quadruple(s, q):
    assert len(s) == len(q)
    sq = tuple(a * b for a, b in zip(s, q, strict=True))
    return (s, half_flip(s), sq, half_flip(sq))


def family_sequences(k):
    s = decode([4] * k + [2, 1, 1] * k + [2, 1, 2] + [1, 1, 2] * (k - 1)
               + [1, 3] + [4] * (k - 1) + [1, 1])
    q = decode([8 * k + 1, 2, 8 * k - 1, 1])
    return quadruple(s, q)


def sequences_39():
    # k=1 in Eliahou's separate 32k+7 construction.
    s = decode([4, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1])
    q = decode([19, 2, 17, 1])
    return quadruple(s, q)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def cyclic_corr(sequences, shift):
    return sum(dot(seq, seq[shift:] + seq[:shift]) for seq in sequences)


def entry(sequences, i, j):
    t = len(sequences[0])
    g, i = divmod(i, t)
    h, j = divmod(j, t)
    which, jsign, isign, sign = BLOCKS[g][h]
    return sign * sequences[which][(jsign * j + isign * i) % t]


def determinant(rows):
    matrix = [[Fraction(x) for x in row] for row in rows]
    result = Fraction(1)
    for j in range(len(matrix)):
        pivot_index = next((i for i in range(j, len(matrix)) if matrix[i][j]), None)
        if pivot_index is None:
            return 0
        if pivot_index != j:
            matrix[j], matrix[pivot_index] = matrix[pivot_index], matrix[j]
            result = -result
        pivot = matrix[j][j]
        result *= pivot
        for i in range(j + 1, len(matrix)):
            multiple = matrix[i][j] / pivot
            matrix[i] = [x - multiple * y for x, y in zip(matrix[i], matrix[j], strict=True)]
    assert result.denominator == 1
    return result.numerator


def family_indices(k):
    t, u = 16 * k + 3, 4 * k
    tetrad = (2 * t + u, 3 * t - u, 3 * t + u, 4 * t - u)
    residual = (u + 1, 3 * u + 2, 3 * u + 3, *(
        g * t + j for g in (1, 2, 3) for j in (u, u + 1, 3 * u + 2)))
    minor = (0, 1, 3, u, u+1, u+2, u+3, u+5, u+6, 3*u+2, 3*u+3, 3*u+4)
    return tetrad, residual, 0, minor


def verify_fixed(sequences, tetrad, selected, normalizer, minor):
    t = len(sequences[0])
    n = 4 * t
    H = [[entry(sequences, i, j) for j in range(n)] for i in range(n)]
    errors = [cyclic_corr(sequences, j) for j in range(1, t)]
    assert all(error % 64 == 0 for error in errors)
    if t == 19:
        assert all(error == 0 for error in errors)
    assert all(dot(H[i], H[j]) == 0 for i, j in combinations(tetrad, 2))
    columns = list(zip(*H, strict=True))
    assert all(dot(columns[i], columns[j]) == 0 for i, j in combinations((*selected, normalizer), 2))
    H = [[x * row[normalizer] for x in row] for row in H]
    assert tuple(j for j in range(n) if sum(H[i][j] < 0 for i in tetrad) % 2) == selected
    half_sums = [sum(H[i][j] for i in tetrad) // 2 for j in range(n)]
    for i in tetrad:
        H[i] = [half_sums[j] - x for j, x in enumerate(H[i])]
    kept = (normalizer, *(j for j in range(n) if j != normalizer and j not in selected))
    A = [[row[j] for j in kept] for row in H]
    R = [[row[j] for j in selected] for row in H]
    if sum(R[0]) % 4 == 0:
        for row in R:
            row[0] *= -1
    reference = A[tetrad[0]]
    A = [[x * y for x, y in zip(a, reference, strict=True)] for a in A]
    assert all(all(x in (-1, 1) for x in row) for row in A)
    assert all(a[0] == 1 for a in A) and all(x == 1 for x in A[tetrad[0]])
    assert all(dot(r, r) == 12 and sum(r) % 4 == 2 for r in R)
    assert all(sum(a < 0 for a in row) % 2 == residual[0] % 2
               for row, residual in zip(A, R, strict=True))
    assert abs(determinant([R[i] for i in minor])) == 65536
    Rt = list(zip(*R, strict=True))
    At = list(zip(*A, strict=True))
    assert all(sum(r) == 0 for r in Rt)
    assert all(dot(r, s) == n * int(i == j) for i, r in enumerate(Rt) for j, s in enumerate(Rt))
    assert all(dot(a, b) % 32 == 0 for a, b in combinations(At, 2))
    assert all((dot(A[i], A[j]) + dot(R[i], R[j])) % 32 == 0
               for i, j in combinations(range(n), 2))
    for a in At:
        products = [dot(a, r) for r in Rt]
        assert all(x % 32 == 0 for x in products)
        assert sum(products) % 64 == 0
    print(f"t={t}, n={n}: exact primitive shadow frame, both augmented Grams mod 32")


@dataclass(frozen=True)
class Affine:
    a: int
    b: int

    def __call__(self, k):
        return self.a * k + self.b

    def __add__(self, other):
        return Affine(self.a + other.a, self.b + other.b)

    def __sub__(self, other):
        return Affine(self.a - other.a, self.b - other.b)

    def __mul__(self, scale):
        return Affine(self.a * scale, self.b * scale)

    def nonnegative_after(self, k0):
        return self.a >= 0 and self(k0) >= 0


X = Affine(1, 0)
C = lambda b: Affine(0, b)
T = X * 16 + C(3)
U = X * 4
BOUNDARIES = (C(0), U, X * 8, X * 8 + C(1), X * 8 + C(2), X * 8 + C(3),
              X * 8 + C(5), X * 12 + C(1), X * 12 + C(2), X * 12 + C(5),
              X * 16 + C(1), X * 16 + C(2), T)
SHIFTS = (C(1), U, U + C(1), X * 8, X * 8 + C(1))
MINOR = (C(0), C(1), C(3), U, U+C(1), U+C(2), U+C(3), U+C(5), U+C(6),
         U*3+C(2), U*3+C(3), U*3+C(4))
PANEL = ((0,U+C(1)),(0,U*3+C(2)),(0,U*3+C(3)),
         *((g,j) for g in (1,2,3) for j in (U,U+C(1),U*3+C(2))))


def check_uniform():
    for k in range(1, 8):
        sequences = family_sequences(k)
        assert all(cyclic_corr(sequences, shift(k)) == 0 for shift in SHIFTS)
        minor = [[entry(sequences, i(k), group*T(k)+j(k)) for group, j in PANEL] for i in MINOR]
        assert abs(determinant(minor)) == 65536
    sign_words = set()
    for k0 in range(8, 16):
        sequences = family_sequences(k0)
        following = family_sequences(k0 + 8)
        for shift in SHIFTS:
            # These are all potential cuts between a pair of s/q/tau runs.
            # Their order stays fixed because the affine slope order agrees.
            cuts = [*BOUNDARIES, *(b - shift for b in BOUNDARIES),
                    *(b + T - shift for b in BOUNDARIES)]
            cuts.sort(key=lambda f: (f(k0), f.a))
            assert all((c - b).nonnegative_after(k0) for b, c in zip(cuts, cuts[1:]))
            assert cyclic_corr(sequences, shift(k0)) == 0
            assert cyclic_corr(following, shift(k0 + 8)) == 0
        minor = []
        for i in MINOR:
            row = []
            for group, j in PANEL:
                which, jsign, isign, sign = BLOCKS[0][group]
                raw = j * jsign + i * isign
                index = raw - T * (raw(k0) // T(k0))
                lo, hi = next((l, h) for l, h in zip(BOUNDARIES, BOUNDARIES[1:])
                              if l(k0) <= index(k0) < h(k0))
                assert (index - lo).nonnegative_after(k0)
                assert (hi - C(1) - index).nonnegative_after(k0)
                row.append(sign * sequences[which][index(k0)])
            minor.append(row)
        assert abs(determinant(minor)) == 65536
        sign_words.add(tuple(sum((x<0)<<i for i,x in enumerate(row)) for row in minor))
    print("uniform exact matching shifts and minor magnitude 65536 for every k >= 1")
    for words in sorted(sign_words):
        print("  sign words:", " ".join(f"{word:03x}" for word in words))


if __name__ == "__main__":
    check_uniform()
    for k in range(1, 5):
        verify_fixed(family_sequences(k), *family_indices(k))
    verify_fixed(sequences_39(), (68,49,107,88),
                 (9,11,29,49,67,69,88,106,108,127,145,147), 2,
                 (0,1,3,9,10,11,12,13,14,28,29,31))
