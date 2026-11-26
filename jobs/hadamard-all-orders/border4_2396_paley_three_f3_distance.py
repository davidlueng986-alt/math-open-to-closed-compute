"""Exact minimum weight with three reciprocal primitive F3 pairs on C299."""

from collections import Counter, defaultdict
from itertools import product

from border4_2396_dual_mod5_forest import reciprocal
from border4_2396_paley_peak32_gates import FACTORS_3
from border4_2396_primitive_field import product as polynomial_product, remainder

X_FACTORS = ((2, 2, 2, 1), (2, 2, 0, 1), (2, 0, 1, 1), (2, 1, 1, 1))
Y_FACTORS = ((2, 0, 0, 1, 0, 1, 0, 2, 2, 1, 1, 1),
             (2, 2, 2, 1, 1, 0, 2, 0, 2, 0, 0, 1))
X_PAIRS = ((0, 3), (1, 2))
Y_POWERS = tuple(pow(3, k, 23) for k in range(11))
Y_INVERSE = tuple(-j % 23 for j in range(23))


def trits(number):
    return tuple(number // 3**i % 3 for i in range(3))


def packed(values):
    return sum(value * 3**i for i, value in enumerate(values))


ADD = tuple(tuple(packed((a + b) % 3 for a, b in zip(trits(u), trits(v), strict=True))
                  for v in range(27)) for u in range(27))
SCALE = tuple((0, u, ADD[u][u]) for u in range(27))


def product_of_factors(factors):
    result = (1,)
    for factor in factors:
        result = polynomial_product(result, factor, 3)
    return result


def check_factors():
    assert product_of_factors(X_FACTORS) == (1,) * 13
    assert product_of_factors(Y_FACTORS) == (1,) * 23
    for a, b in X_PAIRS:
        assert reciprocal(X_FACTORS[a], 3) == X_FACTORS[b]
        assert all(sum(c * a**i for i, c in enumerate(X_FACTORS[a_idx])) % 3 != 0
                   for a_idx in (a, b) for a in range(3))
    assert reciprocal(Y_FACTORS[0], 3) == Y_FACTORS[1]
    assert len(set(Y_POWERS)) == 11 and pow(3, 11, 23) == 1


def ternary_add(left, right):
    a, b = left
    c, d = right
    return ((a & ~(c | d)) | (c & ~(a | b)) | (b & d),
            (b & ~(c | d)) | (d & ~(a | b)) | (a & c))


def ternary_words(generator, dimension):
    plus = sum(1 << i for i, a in enumerate(generator) if a == 1)
    minus = sum(1 << i for i, a in enumerate(generator) if a == 2)
    words = [(0, 0)]
    for j in range(dimension):
        digit = (plus << j, minus << j)
        words += [v for u in words for v in (ternary_add(u, digit), ternary_add(u, digit[::-1]))]
    assert len(words) == 3**dimension
    return words


def fold_y(word):
    return (word & 1) | sum(int(bool(word >> j & 1 or word >> (23 - j) & 1)) << j
                            for j in range(1, 12))


def unfolded_size(mask):
    return 2 * mask.bit_count() - (mask & 1)


def y_small_supports(factor):
    generator = polynomial_product((2, 1), factor, 3)
    words = ternary_words(generator, 11)
    assert Counter((a | b).bit_count() for a, b in words) == {
        0: 1, 9: 2530, 12: 30912, 15: 91080, 18: 49588, 21: 3036}
    small = defaultdict(list)
    for a, b in words[1:]:
        folded = fold_y(a | b)
        if unfolded_size(folded) <= 14:
            small[folded].append((a, b))
    assert min(map(unfolded_size, small)) == 11
    return small


def y_representatives():
    mappings = tuple(tuple(min(j * k % 23, -j * k % 23) for j in range(12))
                     for k in Y_POWERS)
    for mask in range(1 << 12):
        if not 11 <= unfolded_size(mask) <= 14:
            continue
        if all(mask <= sum(1 << row[j] for j in range(12) if mask >> j & 1)
               for row in mappings):
            yield mask


def coefficients(plus, minus, length):
    return tuple((plus >> j & 1) + 2 * (minus >> j & 1) for j in range(length))


def shortened_basis(words):
    basis = []
    pivots = {}
    for p, m in words:
        word = coefficients(p, m, 23)
        v = list(word)
        for k, pivot in pivots.items():
            v = [(a - v[k] * b) % 3 for a, b in zip(v, pivot, strict=True)]
        k = next((j for j, a in enumerate(v) if a), None)
        if k is not None:
            pivots[k] = tuple(a * v[k] % 3 for a in v)
            basis.append(word)
    assert len(basis) <= 2 and len(words) == 3**len(basis) - 1
    return basis


def x_columns(pair):
    generator = product_of_factors(((2, 1), *(f for i, f in enumerate(X_FACTORS)
                                               if i not in pair)))
    rows = {}
    factor = X_FACTORS[pair[0]]
    for p, m in ternary_words(generator, 6):
        c = coefficients(p, m, 13)
        a = packed(remainder(c, factor, 3))
        b = packed(remainder((c[0], *c[:0:-1]), factor, 3))
        assert (a, b) not in rows
        rows[a, b] = c
    assert len(rows) == 729
    weights = tuple(tuple(sum(v != 0 for v in rows[a, b]) for b in range(27))
                    for a in range(27))
    assert min(w for row in weights for w in row if w) == 6
    assert all(weights[a][b] == weights[b][a] for a, b in rows)
    assert all(weights[0][b] == 9 for b in range(1, 27))
    return rows, weights


def shorten(small, weights):
    records = Counter()
    best = 299
    witness = None
    for s in y_representatives():
        words = [word for mask, choices in small.items() if mask & s == mask for word in choices]
        records[unfolded_size(s), len(words)] += 1
        if not words:
            continue
        basis = shortened_basis(words)
        scaled = [tuple(tuple(SCALE[a][c] for c in row) for a in range(27)) for row in basis]
        candidates = (scaled[0][1:] if len(basis) == 1 else
                      (tuple(ADD[a][b] for a, b in zip(x, y, strict=True))
                       for x, y in product(*scaled) if any(x) or any(y)))
        for u in candidates:
            distance = weights[u[0]][u[0]] + 2 * sum(
                weights[u[j]][u[-j]] for j in range(1, 12))
            if distance < best:
                best, witness = distance, u
    assert records == {(11, 0): 40, (11, 2): 2, (12, 0): 30, (12, 2): 12,
                       (13, 2): 40, (13, 8): 2, (14, 8): 30}
    return best, witness


def check_witness(rows, u):
    e = [0] * 299
    for y, a in enumerate(u):
        b = u[Y_INVERSE[y]]
        for x, v in enumerate(rows[a, b]):
            e[(92*x + 208*y) % 299] = v
    assert e[0] == 0 and e[1:] == e[:0:-1]
    assert all(sum(e[i::q]) % 3 == 0 for q in (13, 23) for i in range(q))
    assert sum(v != 0 for v in e) == 84
    direct = tuple(not any(remainder(e, f, 3)) for f in FACTORS_3)
    inverse = tuple(not any(remainder(e, reciprocal(f, 3), 3)) for f in FACTORS_3)
    assert direct == inverse and sum(direct) == 3
    return direct.index(False)


def main():
    check_factors()
    missed = set()
    for factor in Y_FACTORS:
        small = y_small_supports(factor)
        for pair in X_PAIRS:
            rows, weights = x_columns(pair)
            minimum, witness = shorten(small, weights)
            assert minimum == 84 < 15*6
            branch = check_witness(rows, witness)
            missed.add(branch)
            print("remaining primitive pair", branch, "exact ternary distance", minimum)
    assert missed == set(range(4))
    assert 597 - 2*84 == 429


if __name__ == "__main__":
    main()
