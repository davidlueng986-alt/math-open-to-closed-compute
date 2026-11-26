"""Replay the primitive norm obstruction to balanced swaps in any two CRT rows."""

from itertools import combinations

from border4_2396_dual_mod5_forest import FACTORS_5, check_factors
from border4_2396_paley_directed_gate import SPECTRAL_FIXTURES, SPECTRAL_HEAD, SPECTRAL_W_23
from border4_2396_paley_dual_integer import W_13, audit_signs
from border4_2396_paley_negative_norm import N, sign_word
from border4_2396_paley_q13_mod16 import margins
from border4_2396_primitive_field import product, remainder

P, DEG, ROW, COL = 5, 44, 92, 208


def add(*values):
    return tuple(sum(entries) % P for entries in zip(*values, strict=True))


def scale(factor, value):
    return tuple(factor*entry % P for entry in value)


def solve_full_rank(columns, target):
    rows = [list(row) for row in zip(*columns, target, strict=True)]
    size = len(columns)
    for col in range(size):
        pivot = next(i for i in range(col, len(rows)) if rows[i][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        row = rows[col] = scale(pow(rows[col][col], -1, P), rows[col])
        for i, other in enumerate(rows):
            if i != col and other[col]:
                rows[i] = [(a-other[col]*b) % P for a, b in zip(other, row, strict=True)]
    if any(any(row) for row in rows[size:]):
        return None
    return tuple(row[-1] for row in rows[:size])


class PrimitiveField:
    def __init__(self, factor, dimensions):
        self.factor = factor
        self.row_count, self.col_count, self.row_stride, self.col_stride, subdegree = dimensions
        self.subdegree = subdegree
        self.z = tuple(remainder((0,)*i+(1,)+(0,)*DEG, factor, P) for i in range(N))
        self.one = self.z[0]
        self.beta = tuple(self.z[(self.col_stride*j) % N] for j in range(self.col_count))
        self.frobenius = tuple(self.z[i*pow(P, subdegree, N) % N] for i in range(DEG))
        assert self.at(((1, N),)) == self.one
        assert self.z[13] != self.one and self.z[23] != self.one

    def mul(self, a, b):
        return remainder(product(a, b, P), self.factor, P)

    def at(self, terms):
        coefficients = [0]*DEG
        for weight, exponent in terms:
            for i, value in enumerate(self.z[exponent % N]):
                coefficients[i] += weight*value
        return tuple(c % P for c in coefficients)

    def project(self, value):
        image = [0]*DEG
        for weight, basis in zip(value, self.frobenius, strict=True):
            for i, coefficient in enumerate(basis):
                image[i] += weight*coefficient
        return add(image, scale(-1, value))

    def inverse_difference(self, x, y, direction):
        unit = -pow(self.row_count, -1, P)
        step = direction*self.row_stride
        inverse = self.at((unit*j, step*(-x + j*(y-x))) for j in range(1, self.row_count))
        assert self.mul(inverse, self.at(((1, step*x), (-1, step*y)))) == self.one
        return inverse

    def evaluate(self, word, direction):
        return self.at((v, direction*i) for i, v in enumerate(word))

    def pair_solver(self, forward, backward, x, y):
        a = self.inverse_difference(x, y, 1)
        b = self.inverse_difference(x, y, -1)
        p = self.mul(forward, a)
        q = self.mul(backward, b)
        constant = self.mul(p, q)
        pp, qp = map(self.project, (p, q))
        columns = tuple(add(self.mul(qp, self.beta[j]), self.mul(pp, self.beta[-j])) for j in range(self.subdegree))

        def solve(target):
            normal = self.mul(target, self.mul(a, b))
            rhs = self.project(add(normal, scale(-1, constant)))
            coeffs = solve_full_rank(columns, rhs)
            if coeffs is None:
                return False, None
            t = self.at((c, self.col_stride*j) for j, c in enumerate(coeffs))
            t_star = self.at((c, -self.col_stride*j) for j, c in enumerate(coeffs))
            norm = self.mul(add(p, t), add(q, t_star))
            return True, coeffs if norm == normal else None

        return solve


def main():
    check_factors()
    u, v, w = map(sign_word, (*SPECTRAL_HEAD, SPECTRAL_FIXTURES[0][1]))
    assert margins((w,), 13) == (W_13,) and margins((w,), 23) == (SPECTRAL_W_23,)
    raw = audit_signs(u, v, w, (17, -5, -21))
    assert (max(map(abs, raw)), raw.count(0), sum(r*r for r in raw)) == (32, 129, 179200)
    for dimensions in ((13, 23, ROW, COL, 22), (23, 13, COL, ROW, 4)):
        for index, factor in enumerate(FACTORS_5):
            check_orientation(dimensions, index, factor, u, v, w)


def check_orientation(dimensions, index, factor, u, v, w):
    field = PrimitiveField(factor, dimensions)
    row_count, col_count, row_stride, col_stride, _ = dimensions
    uf, vf, wf = (field.evaluate(word, 1) for word in (u, v, w))
    ur, vr, wr = (field.evaluate(word, -1) for word in (u, v, w))
    target = scale(pow(2, -1, P), add(scale(1196, field.one),
                                    scale(-1, field.mul(uf, ur)), scale(-1, field.mul(vf, vr))))
    incompatible = 0
    controlled = False
    for x, y in combinations(range(row_count), 2):
        solve = field.pair_solver(wf, wr, x, y)
        consistent, solution = solve(target)
        assert solution is None
        incompatible += not consistent
        if controlled:
            continue
        flags = [w[(row_stride*y+col_stride*j) % N]-w[(row_stride*x+col_stride*j) % N]
                 for j in range(col_count)]
        if 2 in flags and -2 in flags:
            positions = (flags.index(2), flags.index(-2))
            changed = list(w)
            for j in positions:
                a, b = (row_stride*x+col_stride*j) % N, (row_stride*y+col_stride*j) % N
                changed[a], changed[b] = changed[b], changed[a]
            assert margins((changed,), 13) == (W_13,) and margins((changed,), 23) == (SPECTRAL_W_23,)
            control = field.mul(field.evaluate(changed, 1), field.evaluate(changed, -1))
            assert solve(control)[1] is not None
            controlled = True
    assert incompatible == (0 if row_count == 13 else 253) and controlled
    pair_count = row_count*(row_count-1)//2
    print(f"Primitive mod 5 factor {index}, side {row_count}: {pair_count} full-rank systems, "
          f"{incompatible} inconsistent; others fail the norm; physical control recovered")


if __name__ == "__main__":
    main()
