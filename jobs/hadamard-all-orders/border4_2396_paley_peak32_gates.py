"""Exact two-factor finite gates for the published peak-32 Paley witness."""

from itertools import product
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

from border4_2396_dual_mod5_forest import FACTORS_5, check_factors, reciprocal
from border4_2396_paley_directed_gate import SPECTRAL_FIXTURES, SPECTRAL_HEAD
from border4_2396_paley_negative_norm import N, periodic, sign_word
from border4_2396_primitive_field import binomial, order, product as multiply, remainder

FACTORS_3 = tuple(tuple(map(int, digits)) for digits in (
    "2002010110221121101110022110111101",
    "2002022020022022020011212000022211",
    "2000021201222120000001222101202121",
    "2001001102022100000221120010011021",
))

BOX_CERTIFICATES = (
    ((0, 1), 12, (11,24,28,29,32,38,43,45,62,64,76,81,114,126,136,20,80,40,9,41,5)),
    ((0, 2), 12, (11,14,24,28,29,38,45,62,64,76,81,126,108,136,44,75,1,54,5,9,73,133)),
    ((1, 2), 11, (11,14,24,28,29,38,45,62,64,76,81,133,136,126,40,32,58,12,34)),
)
FEEDBACK_LAGS = (2, 4, 17, 33, 46, 52, 97, 142)


def peak32_words():
    _, w, _, expected, _ = SPECTRAL_FIXTURES[0]
    assert expected == (373, 129, 32, 179200)
    return tuple(map(sign_word, (*SPECTRAL_HEAD, w)))


def anchored_residual(words):
    result = periodic(words + (words[-1],))
    result[0] -= 1196
    assert result[0] == 0 and result == result[:1] + result[:0:-1]
    assert all(value % 8 == 0 for value in result) and max(map(abs, result)) == 32
    assert all(sum(result[i::q]) == 0 for q in (13, 23) for i in range(q))
    return tuple(value // 8 for value in result[:150])


def subtract(left, right, scale, prime):
    return [(x - scale*y) % prime for x, y in zip(left, right, strict=True)]


def kernel(columns, prime):
    """Column elimination, retaining physical preimages of eliminated columns."""
    pivots = {}
    generators = []
    for i, line in enumerate(columns):
        physical = [0] * len(columns)
        physical[i] = 1
        value = [x % prime for x in line]
        for p, (column, prior) in sorted(pivots.items()):
            if value[p]:
                physical = subtract(physical, prior, value[p], prime)
                value = subtract(value, column, value[p], prime)
        for p, entry in enumerate(value):
            if entry:
                scale = pow(entry, -1, prime)
                pivots[p] = ([scale*x % prime for x in value],
                             [scale*x % prime for x in physical])
                break
        else:
            generators.append(tuple(physical))
    return generators


def inverse(matrix, prime):
    width = len(matrix)
    table = [list(row) + [int(i == j) for j in range(width)] for i, row in enumerate(matrix)]
    for i in range(width):
        pivot = next(j for j in range(i, width) if table[j][i])
        table[i], table[pivot] = table[pivot], table[i]
        scale = pow(table[i][i], -1, prime)
        table[i] = [scale*x % prime for x in table[i]]
        for j in range(width):
            if i != j and table[j][i]:
                table[j] = subtract(table[j], table[i], table[j][i], prime)
    assert all(row[:width] == [int(i == j) for j in range(width)] for i, row in enumerate(table))
    return tuple(tuple(row[width:]) for row in table)


def column(lag, factors, prime):
    quotient = tuple(int((lag - i) % q == 0) + int((-lag - i) % q == 0)
                     for q in (13, 23) for i in range(q))
    representative = tuple(int(i in (lag, N - lag)) for i in range(N))
    return quotient + tuple(x for factor in factors for x in remainder(representative, factor, prime))


def interval(value):
    return range(min(0, value), max(0, value) + 1)


def prove_boxes(e):
    check_factors()
    support = tuple(d for d in range(1, 150) if e[d])
    assert len(support) == 117
    index = {d: i for i, d in enumerate(support)}
    for pairs, dimension, boxes in BOX_CERTIFICATES:
        factors = tuple(FACTORS_5[i] for i in pairs)
        basis = kernel(tuple(column(d, factors, 5) for d in support), 5)
        assert len(basis) == dimension and len(set(boxes)) == len(boxes)
        forms = tuple(zip(*basis, strict=True))
        anchors = boxes[:dimension]
        change = inverse(tuple(forms[index[d]] for d in anchors), 5)
        checks = []
        for d in boxes[dimension:]:
            form = forms[index[d]]
            row = tuple(sum(a * change[i][j] for i, a in enumerate(form)) % 5
                        for j in range(dimension))
            checks.append((row, frozenset(x % 5 for x in interval(e[d]))))
        checked = 0
        for parameters in product(*(interval(e[d]) for d in anchors)):
            checked += 1
            if all(sum(x*y for x, y in zip(row, parameters, strict=True)) % 5 in allowed
                   for row, allowed in checks):
                assert not any(parameters)
        assert checked == 2**dimension
        print(f"F5 factors {pairs}: {len(boxes)} boxes, {checked} parameter cases, only zero")


def check_factors_3():
    assert (order(3, 13), order(3, 23), order(3, N)) == (3, 11, 33)
    companions = tuple(reciprocal(f, 3) for f in FACTORS_3)
    factors = FACTORS_3 + companions
    assert len(set(factors)) == 8 and all(len(f) == 34 and f[-1] == 1 for f in factors)
    total = (1,)
    for factor in factors:
        total = multiply(total, factor, 3)
    assert multiply(total, multiply(binomial(13), binomial(23), 3), 3) == (
        multiply(binomial(N), binomial(1), 3)
    )


def prove_threes(e):
    check_factors_3()
    support = tuple(d for d in range(1, 150) if abs(e[d]) >= 2)
    assert len(support) == 84 and sum(abs(e[d]) == 1 for d in range(1, 150)) == 33
    for indexes in ((0, 1), (0, 3)):
        factors = tuple(FACTORS_3[i] for i in indexes)
        assert not kernel(tuple(column(d, factors, 3) for d in support), 3)
    high = {d for d in support if abs(e[d]) >= 3}
    deleted = set(FEEDBACK_LAGS)
    assert len(high) == 41 and deleted <= high and all(abs(e[d]) == 4 for d in deleted)
    edges = []
    for d in high - deleted:
        x, y = min(d % 13, -d % 13), 7 + min(d % 23, -d % 23)
        edges.append((x, y) if e[d] > 0 else (y, x))
    vertices = set(range(19))
    while vertices:
        tails = vertices.difference(v for u, v in edges if u in vertices)
        assert tails
        vertices.difference_update(tails)
    print("Two F3 pairs are injective on 84 lags; deleting eight even high lags leaves a DAG")


def prove_neighborhood(words):
    source = Path(__file__).with_name("border4_2396_paley_peak32_neighborhood.cpp")
    with TemporaryDirectory() as directory:
        binary = Path(directory) / "neighborhood"
        subprocess.run((os.environ.get("CXX", "c++"), "-std=c++20", "-O3", str(source),
                        "-o", str(binary)), check=True)
        data = "\n".join(" ".join(map(str, word)) for word in words) + "\n"
        output = subprocess.run((str(binary),), input=data, text=True, capture_output=True,
                                check=True).stdout.strip()
    assert output == "complete rectangles=2487 pairs=2927826 six=94921 peak24=0"
    print(output)


def main():
    words = peak32_words()
    e = anchored_residual(words)
    prove_boxes(e)
    prove_threes(e)
    if sys.argv[1:] == ["--neighborhood"]:
        prove_neighborhood(words)


if __name__ == "__main__":
    main()
