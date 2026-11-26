"""Verify the four auxiliary blocks and an independent mixed Paley order-12 control."""
from collections import defaultdict
from itertools import combinations, product
from math import isqrt


ORDER = 2396
FIRST = (4, 18, 30, 34)


def dot(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True))


def transpose(rows):
    return tuple(zip(*rows, strict=True))


def multiply(left, right):
    return tuple(tuple(dot(row, col) for col in transpose(right)) for row in left)


def orient(v):
    sign = 1 if next(value for value in v if value) > 0 else -1
    return tuple(sign * value for value in v)


def orthogonal(frame):
    return all(dot(a, b) == 0 for a, b in combinations(frame, 2))


def directions(parity, allowed):
    radius = isqrt(ORDER)
    possible = range(-radius + parity, radius + 1, 2)
    norms = defaultdict(list)
    for a, b in product(possible, repeat=2):
        norms[a*a + b*b].append((a, b))
    return {orient(left + right) for norm, lefts in norms.items()
            for left, right in product(lefts, norms.get(ORDER - norm, ()))
            if abs(dot(FIRST, left + right)) in allowed}


def align(even, odd):
    h = tuple(tuple(dot(e, o) // (ORDER // 2) for o in odd) for e in even)
    assert all(value in (1, -1) for row in h for value in row) and orthogonal(h)
    e_sign = [row[0] * h[0][0] for row in h]
    o_sign = h[0]
    assert e_sign[0] == 1
    e = tuple(tuple(s * value for value in v) for s, v in zip(e_sign, even, strict=True))
    o = tuple(tuple(s * value for value in v) for s, v in zip(o_sign, odd, strict=True))
    h = tuple(tuple(dot(v, w) // (ORDER // 2) for w in o) for v in e)
    assert h[0] == (1,)*4 and all(row[0] == 1 for row in h)
    return transpose(e), transpose(o), h


def frames():
    even = directions(0, {0, ORDER})
    odd = directions(1, {ORDER // 2})
    assert len(even) == 7 and len(odd) == 16
    frame_pairs = []
    for rest in combinations(sorted(even - {FIRST}), 3):
        e = (FIRST, *rest)
        if not orthogonal(e):
            continue
        compatible = [v for v in sorted(odd) if all(abs(dot(v, w)) == ORDER // 2 for w in e)]
        for o in combinations(compatible, 4):
            if orthogonal(o):
                frame_pairs.append(align(e, o))
    assert len(frame_pairs) == 4
    return frame_pairs, even | odd


def verify_directions():
    r = tuple(tuple(1 - 2 * (i == j) for j in range(4)) for i in range(4))
    pairs, all_directions = frames()
    reached = set()
    for e, o, h in pairs:
        assert multiply(e, h) == tuple(tuple(2*value for value in row) for row in o)
        even, odd = set(map(orient, transpose(e))), set(map(orient, transpose(o)))
        k = tuple(tuple(value // 2 for value in row) for row in multiply(e, r))
        assert orthogonal(k) and all(dot(row, row) == ORDER for row in k)
        assert all(value % 2 for row in k for value in row)
        assert all(sum(value % 4 == 3 for value in row) % 2 for row in k)
        observed = {0: set(), 1: set()}
        for f in product((1, -1), repeat=4):
            beta = tuple(dot(row, f) for row in k)
            assert all(value % 2 == 0 for value in beta)
            observed[sum(value == -1 for value in f) % 2].add(orient(tuple(value//2 for value in beta)))
        assert observed[1] == even and observed[0] == odd
        anchoring = r[0]
        assert tuple(dot(row, anchoring) for row in k) == tuple(2 * value for value in FIRST)
        reached.update(even | odd)
    assert reached == all_directions
    print('2396 auxiliary frame pairs: four integer blocks cover all 23 exact next directions')


def paley_order12():
    residues = {i * i % 11 for i in range(1, 11)}
    return [[1] * 12, *[[-1, *[
        1 if i == j or (j - i) % 11 in residues else -1
        for j in range(11)
    ]] for i in range(11)]]


def restrict(word, indices):
    return [word[i] for i in indices]


def find_h12_control(columns):
    for top in ((0, *extra) for extra in combinations(range(1, 12), 3)):
        bottom = [i for i in range(12) if i not in top]
        a_cols = [restrict(c, top) for c in columns]
        b_cols = [restrict(c, bottom) for c in columns]
        for old in ((0, *extra) for extra in combinations(range(1, 12), 3)):
            a = [a_cols[j] for j in old]
            if not orthogonal(a):
                continue
            b = [b_cols[j] for j in old]
            assert orthogonal(b)
            possible = [d for d in product((1, -1), repeat=8) if d[0] == 1 and all(dot(d, x) == 0 for x in b)]
            for d in combinations(possible, 4):
                if not orthogonal(d):
                    continue
                future = [j for j in range(12) if j not in old]
                z = [[dot(c, b_cols[j]) // 2 for c in d] for j in future]
                if {item[0] % 2 for item in z} == {0, 1}:
                    return top, old, a, b, d, future, a_cols, b_cols, z
    raise ValueError('no mixed control')


def control_frames(z):
    even = sorted({orient(item) for item in z if item[0] % 2 == 0})
    odd = sorted({orient(item) for item in z if item[0] % 2 == 1})
    assert len(even) == len(odd) == 4 and orthogonal(even) and orthogonal(odd)
    h = [[dot(e, o) // 6 for o in odd] for e in even]
    assert orthogonal(h)
    e_signs = [row[0] * h[0][0] for row in h]
    o_signs = h[0]
    e = transpose([[s * x for x in column] for s, column in zip(e_signs, even, strict=True)])
    o = transpose([[s * x for x in column] for s, column in zip(o_signs, odd, strict=True)])
    h = [[x // 6 for x in row] for row in multiply(transpose(e), o)]
    assert h[0] == [1] * 4 and [row[0] for row in h] == [1] * 4
    return e, o, h


def verify_small_control():
    columns = transpose(paley_order12())
    assert all(dot(col, col) == 12 for col in columns) and orthogonal(columns)
    top, old, a_cols, b_cols, d_cols, future, x_cols, y_cols, z = find_h12_control(columns)
    assert set(top) == set(old) == {0, 1, 2, 3}
    e, _, _ = control_frames(z)
    e_t = transpose(e)
    r = [[1 - 2 * (i == j) for j in range(4)] for i in range(4)]
    k = [[value // 2 for value in row] for row in multiply(e, r)]
    assert orthogonal(k) and all(dot(row, row) == 12 for row in k)
    g = [[dot(e_col, z_col) for z_col in z] for e_col in e_t]
    f_scaled = multiply(r, g)
    assert all(abs(value) == 12 for row in f_scaled for value in row)
    f = [[value // 12 for value in row] for row in f_scaled]
    x = transpose([x_cols[j] for j in future])
    assert orthogonal((*x, *f))
    assert all(dot(row, row) == 8 for row in (*x, *f))
    ba = multiply(transpose(b_cols), a_cols)
    dk = multiply(transpose(d_cols), k)
    left = multiply(ba, x)
    right = multiply(dk, f)
    numerator = [[d - c for c, d in zip(l, r, strict=True)] for l, r in zip(left, right, strict=True)]
    assert all(value % 16 == 8 for row in numerator for value in row)
    y = [[value // 8 for value in row] for row in numerator]
    assert tuple(map(tuple, y)) == transpose([y_cols[j] for j in future])
    options = multiply(list(product((1,-1), repeat=4)), g)
    sign_kernels = [[v // 12 for v in option] for option in options if all(abs(v) == 12 for v in option)]
    assert len(sign_kernels) == 8
    assert {tuple(row) for row in sign_kernels} == {tuple(s * x for x in row) for row in f for s in (1,-1)}
    t = [*x, *f]
    known_index = next(i for i, col in enumerate(z) if col[0] % 2 == 0)
    known = transpose(t)[known_index]
    # P = W T, where the first four and last four columns of W are -BA^T and DK.
    w = [tuple(-value for value in b) + tuple(d) for b, d in zip(ba, dk, strict=True)]
    solutions, odd_quotients = [], []
    for z_bits in product((0, 1), repeat=8):
        subset = tuple(s * bit for s, bit in zip(known, z_bits, strict=True))
        nudge = tuple(dot(row, subset) for row in w)
        trial = tuple(s - 2 * value for s, value in zip(known, subset, strict=True))
        p = tuple(dot(row, trial) for row in w)
        if all(value % 8 == 0 for value in nudge):
            solutions.append(trial)
            assert sum(z_bits) in (0, 4, 8)
            assert all(value in (-8, 8) for value in p)
        if all(value % 16 == 8 for value in p):
            odd_quotients.append(trial)
    assert solutions == odd_quotients
    assert set(solutions) == {tuple(s * v for v in col) for col in transpose(t) for s in (1, -1)}
    for a, b in combinations(solutions, 2):
        assert dot(a, b) in (-8, 0)
    print('auxiliary H12 control: 8 sign kernel rows; 16 binary solutions in 8 orthogonal directions')



def verify():
    verify_directions()
    verify_small_control()


if __name__ == "__main__":
    verify()
