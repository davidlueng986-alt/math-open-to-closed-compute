"""Replay the full-period direct Goethals–Seidel residuals and arithmetic screens."""

from itertools import combinations_with_replacement
import json
from math import isqrt
from pathlib import Path

from verify import goethals_seidel, signs, verify_orthogonal


P = 599
DATA = Path(__file__).with_name("direct_2396_cyclic_data.json")
CASES = {
    "energy": ((1, 3, 19, 45), 1330, 231, 6),
    "amplitude": ((1, 3, 19, 45), 1356, 251, 5),
}


def quarter_correlations(words):
    length = len(words[0])
    mask = (1 << length) - 1
    negatives = [sum((x == '-') << i for i, x in enumerate(word)) for word in words]
    target = sum(x.bit_count() for x in negatives) - length
    return [sum((x & ((x << d) | (x >> (length-d))) & mask).bit_count()
                for x in negatives) - target for d in range(length)]


def check_direct_words():
    data = json.loads(DATA.read_text())
    assert data.keys() == CASES.keys()
    for name, words in data.items():
        assert all(len(word) == P and set(word) == {'+', '-'} for word in words)
        sums = tuple(sum(signs(w)) for w in words)
        given_sums, square, nonzero, peak = CASES[name]
        assert given_sums == sums
        assert all(x > 0 and x % 2 for x in sums)
        assert sum(x*x for x in sums) == 4*P
        residual = quarter_correlations(words)
        assert residual[0] == P and sum(residual[1:]) == 0
        assert residual[1:] == residual[:0:-1]
        pair_residual = residual[1:(P+1)//2]
        assert (sum(x*x for x in pair_residual),
                sum(x != 0 for x in pair_residual),
                max(map(abs, pair_residual))) == (square, nonzero, peak)
        for q in (2, 3, 7):
            # Reduction of E by 1+z+...+z^(P-1) subtracts its top coefficient.
            e = [0, *residual[1:]]
            assert any((x-e[-1]) % q for x in e[:-1])
        print(f"Direct cyclic {name}: sums {sums}, {nonzero} nonzero lag pairs, "
              f"raw peak {4*peak}, raw squared error {32*square}")


def check_arithmetic():
    assert all(P % d for d in range(2, isqrt(P)+1))
    for q in (2, 3):
        assert pow(q, 299, P) == 1
        assert pow(q, 13, P) != 1 and pow(q, 23, P) != 1
    assert pow(7, 598, P) == 1
    assert all(pow(7, 598//d, P) != 1 for d in (2, 13, 23))
    options = [sums for sums in combinations_with_replacement(range(1, isqrt(4*P)+1, 2), 4)
               if sum(x*x for x in sums) == 4*P]
    assert len(options) == 28 and all(sums.count(1) <= 1 for sums in options)
    for order, options_expected in ((13, {1, 25, 27}), (23, {1, 45, 47})):
        orbit_sums = {s for s in range(1, isqrt(4*P)+1, 2) if s % (2*order) in (1, 2*order-1)}
        assert orbit_sums == options_expected
        assert not any(set(sums) <= orbit_sums for sums in options)
        assert max(sum(s in orbit_sums for s in sums) for sums in options) == 2
    print("Direct cyclic: 28 sums, neither odd affine multiplier permits four invariant words")


def check_control():
    words = ('+--+-++', '+--+-++', '+--+-++', '-++++++')
    assert quarter_correlations(words) == [7]+[0]*6
    assert verify_orthogonal(28, goethals_seidel(tuple(map(signs, words)))) == 378


if __name__ == "__main__":
    check_arithmetic()
    check_control()
    check_direct_words()
