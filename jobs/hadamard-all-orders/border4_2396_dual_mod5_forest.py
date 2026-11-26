"""Replay smaller-modulus lifting conditions for the dual-quotient residual."""

from functools import reduce

from border4_2396 import periodic
from border4_2396_dual_peak40 import PEAK40_293_MASKS, PEAK40_325_MASKS, PEAK40_LOW_ENERGY_MASKS
from border4_2396_dual_peak48 import LOW_ENERGY_MASKS, PEAK48_MASKS, PEAK48_MORE_MOD16_MASKS
from border4_2396_dual_quotient import dual_words, endpoints
from border4_2396_primitive_field import binomial, order, primitive_factor, product, remainder


FACTORS_5 = tuple(tuple(map(int, digits)) for digits in (
    "114214313111312001234224003243332021213322221",
    "103400401440024014423424124400342334411330441",
    "100342403010214024241303334332320114330032421",
))


def reciprocal(poly, modulus):
    scale = pow(poly[0], -1, modulus)
    return tuple(value * scale % modulus for value in reversed(poly))


def check_factors():
    assert (order(5, 13), order(5, 23), order(5, 299)) == (4, 22, 44)
    assert all(pow(5, exponent, 299) != 298 for exponent in range(44))
    factors = (*FACTORS_5, *(reciprocal(poly, 5) for poly in FACTORS_5))
    assert len(set(factors)) == 6 and all(len(factor) == 45 and factor[-1] == 1 for factor in factors)
    cyclotomic = reduce(lambda left, right: product(left, right, 5), factors, (1,))
    assert product(cyclotomic, product(binomial(13), binomial(23), 5), 5) == (
        product(binomial(299), binomial(1), 5)
    )


def residual(words):
    corr = periodic(words)
    assert corr[0] == 597 and all((value+2) % 4 == 0 for value in corr[1:])
    e = (0, *((value+2)//4 for value in corr[1:]))
    assert all(sum(e[i::q]) == 0 for q in (13, 23) for i in range(q))
    return e


def forest(edges):
    roots = list(range(19))
    tree = []
    chords = []

    def root(i):
        while roots[i] != i:
            i = roots[i]
        return i

    for d in edges:
        left, right = map(root, endpoints(d))
        if left == right:
            chords.append(d)
        else:
            roots[left] = right
            tree.append(d)
    return tuple(tree), tuple(chords)


def verify():
    check_factors()
    factor_7 = primitive_factor(7)
    cases = (
        ("Peak 40, 293 mod16", PEAK40_293_MASKS, 5, 13, 0, (33, 35, 36)),
        ("Peak 40, 325 mod16", PEAK40_325_MASKS, 5, 13, 2, (36, 34, 33)),
        ("Peak 40, lower energy", PEAK40_LOW_ENERGY_MASKS, 5, 7, 0, (31, 34, 34)),
        ("Peak 48, 317 mod16", PEAK48_MASKS, 5, 5, 0, (36, 34, 37)),
        ("Peak 48, 365 mod16", PEAK48_MORE_MOD16_MASKS, 5, 7, 0, (29, 34, 38)),
        ("Peak 80, 165 exact", LOW_ENERGY_MASKS, 5, 8, 0, (33, 35, 32)),
        ("Peak 80, 165 exact", LOW_ENERGY_MASKS, 7, 2, 0, (118,)),
    )
    for label, masks, prime, high_count, cycle_rank, counts in cases:
        e = residual(dual_words(masks))
        high = tuple(d for d in range(1, 150) if abs(e[d]) >= prime)
        _, chords = forest(high)
        assert (len(high), len(chords)) == (high_count, cycle_rank)
        factors = FACTORS_5 if prime == 5 else (factor_7,)
        got = tuple(sum(bool(v) for v in remainder(e, factor, prime)) for factor in factors)
        assert got == counts
        print(f"{label}: p={prime}, high lags {high}, chord lags {chords}, nonzero factor residuals {got}")


if __name__ == "__main__":
    verify()
