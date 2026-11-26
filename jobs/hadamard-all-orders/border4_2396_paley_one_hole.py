"""Replay the Paley one-hole primitive norm rigidity and support reduction."""

from itertools import product as choices
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from border4_2396 import periodic
from border4_2396_dual_mod5_forest import FACTORS_5, check_factors, reciprocal
from border4_2396_primitive_field import primitive_factor, product, remainder

N = 299
FIELD = 599
MODULUS = 5


def character(value):
    return {0: 0, 1: 1, FIELD - 1: -1}[pow(value, N, FIELD)]


def paley_words():
    assert (pow(2, N, FIELD), pow(2, 13, FIELD), pow(2, 23, FIELD)) == (1, 405, 212)
    powers = tuple(pow(2, i, FIELD) for i in range(N))
    one_hole = tuple(character(x - 1) for x in powers)
    full = tuple(character(-x - 1) for x in powers)
    assert one_hole[0] == 0 and all(abs(x) == 1 for x in one_hole[1:] + full)
    assert all(one_hole[i] == -one_hole[-i] and full[i] == full[-i] for i in range(N))
    assert periodic((one_hole, full)) == [597] + [-2] * (N - 1)
    return one_hole, full


def trimmed(poly):
    coefficients = list(poly)
    while coefficients and coefficients[-1] == 0:
        coefficients.pop()
    return tuple(coefficients)


def subtract(left, right):
    width = max(len(left), len(right))
    a = left + (0,) * (width - len(left))
    b = right + (0,) * (width - len(right))
    return trimmed((u - v) % MODULUS for u, v in zip(a, b, strict=True))


def divide(dividend, divisor):
    tail = list(trimmed(value % MODULUS for value in dividend))
    quotient = [0] * max(0, len(tail) - len(divisor) + 1)
    scale = pow(divisor[-1], -1, MODULUS)
    while len(tail) >= len(divisor):
        shift = len(tail) - len(divisor)
        coeff = tail[-1] * scale % MODULUS
        quotient[shift] = coeff
        for i, value in enumerate(divisor):
            tail[shift + i] = (tail[shift + i] - coeff * value) % MODULUS
        while tail and tail[-1] == 0:
            tail.pop()
    return tuple(quotient), tuple(tail)


def inverse_mod_factor(poly, factor):
    previous, current = factor, divide(poly, factor)[1]
    left, right = (), (1,)
    while current:
        quotient, residual = divide(previous, current)
        previous, current = current, residual
        correction = product(quotient, right, MODULUS) if right else ()
        left, right = right, subtract(left, correction)
    assert len(previous) == 1
    scaled = tuple(value * pow(previous[0], -1, MODULUS) % MODULUS for value in left)
    return divide(scaled, factor)[1]


def primitive_parts(word):
    cyclic = (MODULUS - 1,) + (0,) * (N - 1) + (1,)
    for first in FACTORS_5:
        pair = [0] * N
        for factor in (first, reciprocal(first, MODULUS)):
            quotient, tail = divide(cyclic, factor)
            assert not tail
            projection = product(quotient, inverse_mod_factor(quotient, factor), MODULUS)
            for i, value in enumerate(product(projection, word, MODULUS)):
                pair[i % N] = (pair[i % N] + value) % MODULUS
        yield tuple(pair)


def index(x, y):
    return (92 * x + 208 * y) % N


def physical_skew_words(spectrum):
    # The unprescribed proper component is a(x)+b(y). Normalizing a(0)=b(0)=0
    # leaves two choices per nonzero opposite x or y pair on the axes.
    signs = (1, MODULUS - 1)
    assert spectrum[0] == 0 and all((spectrum[i] + spectrum[-i]) % MODULUS == 0
                                   for i in range(N))
    x_axis = [tuple((value - spectrum[index(x, 0)]) % MODULUS for value in signs)
              for x in range(1, 7)]
    y_axis = [tuple((value - spectrum[index(0, y)]) % MODULUS for value in signs)
              for y in range(1, 12)]
    for positive_x in choices(*x_axis):
        a = (0, *positive_x, *(-u for u in reversed(positive_x)))
        b_deck = []
        for y, allowed in enumerate(y_axis, 1):
            feasible = tuple(b for b in allowed
                             if all((spectrum[index(x, y)] + a[x] + b) % MODULUS in signs
                                    for x in range(13)))
            if not feasible:
                break
            b_deck.append(feasible)
        else:
            for positive_y in choices(*b_deck):
                b = (0, *positive_y, *(-u for u in reversed(positive_y)))
                word = tuple((spectrum[i] + a[i % 13] + b[i % 23]) % MODULUS
                             for i in range(N))
                assert word[0] == 0 and all(u in signs for u in word[1:])
                yield tuple(u if u < 2 else u - MODULUS for u in word)


def verify_primitives(one_hole):
    # The q7 proof uses the two degree-132 reciprocal factors and the fact
    # that neither family of proper fibres contains a constant sign row.
    primitive_factor(7)
    maxima = tuple(max(abs(sum(one_hole[i::q])) for i in range(q)) for q in (13, 23))
    assert maxima == (5, 7)
    assert (5 < N // 13, 7 < N // 23) == (True, True)

    check_factors()
    assert all(index(x, y) % 13 == x and index(x, y) % 23 == y
               for x in range(13) for y in range(23))
    parts = tuple(primitive_parts(one_hole))
    factors = FACTORS_5 + tuple(reciprocal(factor, MODULUS) for factor in FACTORS_5)
    for j, part in enumerate(parts):
        for k, factor in enumerate(factors):
            expected = remainder(one_hole if j == k % 3 else (0,) * N, factor, MODULUS)
            assert remainder(part, factor, MODULUS) == expected
    counts = []
    for signs in choices((1, -1), repeat=3):
        spectrum = tuple(sum(sign * value for sign, value in zip(signs, column, strict=True)) % MODULUS
                         for column in zip(*parts, strict=True))
        words = tuple(physical_skew_words(spectrum))
        expected = () if len(set(signs)) != 1 else (tuple(signs[0] * u for u in one_hole),)
        assert words == expected
        counts.append(len(words))
    print(f"Primitive norm rigidity: mod7 fibre maxima {maxima}, mod5 pair sign counts {tuple(counts)}")


def verify_support_reduction(one_hole, full):
    a = tuple(full[0] * (u + v) // 2 if i else 0
              for i, (u, v) in enumerate(zip(one_hole, full, strict=True)))
    support = tuple(bool(u) for u in a)
    assert not support[0] and all(support[i] ^ support[-i] for i in range(1, N))
    assert a == tuple(support[i] * (2 * support[i * 150 % N] - 1) for i in range(N))
    assert (a.count(1), a.count(-1)) == (74, 75)
    correlations = periodic((a,))
    assert all(2 * correlations[i] == -1 - a[i] - a[-i] for i in range(1, N))


def main():
    one_hole, full = paley_words()
    verify_primitives(one_hole)
    verify_support_reduction(one_hole, full)
    source = Path(__file__).with_suffix(".cpp")
    with TemporaryDirectory() as directory:
        executable = Path(directory) / "skew-support"
        subprocess.run((os.environ.get("CXX", "c++"), "-O3", "-std=c++20", str(source),
                        "-o", str(executable)), check=True)
        for args, expected in (
            ((), "support decks 528 22 12 exact 264 known variants 264 novel 0"),
            (("all-small",), "support decks 4 2048 64 exact 2 known variants 264 novel 0"),
        ):
            output = subprocess.check_output((str(executable), *args), text=True).strip()
            assert output == expected
            print(output)


if __name__ == "__main__":
    main()
