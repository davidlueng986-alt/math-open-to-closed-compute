"""Exact replay for a one-lag near-64 Golay quadruple of length 599."""

from fractions import Fraction
from math import factorial, isqrt


LENGTH = 599
ALL = (1 << LENGTH) - 1
TEMPLATES = ((4,), (2, 1, 1), (4,), (2, 1, 1), (4,), (1, 2, 1), (4,), (1, 2, 1))
COUNTS = (18, 19, 18, 19, 17, 19, 18, 18)
RUNS_AFTER = ((), (1, 5), (), (), (3,), (3,), (3,), ())


def run_word(runs):
    value = length = 0
    for i, run in enumerate(runs):
        if i % 2:
            value |= ((1 << run) - 1) << length
        length += run
    assert length == LENGTH
    return value


def rotate(value, distance):
    return (value >> distance) | ((value & ((1 << distance) - 1)) << (LENGTH - distance))


def source_words():
    s = run_word([run for template, count, after in zip(TEMPLATES, COUNTS, RUNS_AFTER, strict=True)
                  for run in template * count + after])
    return s, run_word((299, 2, 297, 1)), run_word((300, 299))


def exact_repair_bounds(coefficients):
    """Bound the source trace against an exactly orthogonal sign matrix."""
    assert dict(coefficients)[4] == -2240

    def arctangent_interval(divisor):
        upper = sum(Fraction((-1)**i, (2*i + 1) * divisor**(2*i + 1)) for i in range(23))
        return upper - Fraction(1, 47 * divisor**47), upper

    a_low, a_high = arctangent_interval(5)
    b_low, b_high = arctangent_interval(239)
    pi_lower = Fraction(3141592653589793, 10**15)
    pi_error = Fraction(1, 10**15)
    assert pi_lower < 16*a_low - 4*b_high < 16*a_high - 4*b_low < pi_lower + pi_error

    scale = 10**12
    padding = pi_error + Fraction(4**42, factorial(42))
    cosine = []
    for j in range((LENGTH + 1) // 2):
        argument = 2 * pi_lower * j / LENGTH
        center = sum((-1)**i * argument**(2*i) / factorial(2*i) for i in range(21))
        lower = ((center - padding) * scale) // 1
        upper = -((-(center + padding) * scale) // 1)
        cosine.append((lower, upper))

    n = 4 * LENGTH
    singular_bounds = []
    for k in range(LENGTH):
        eigenvalue_upper = n * scale
        for d, value in coefficients:
            j = (d * k) % LENGTH
            interval = cosine[min(j, LENGTH - j)]
            bound = interval[1 if value > 0 else 0]
            eigenvalue_upper += 2 * value * bound
        assert eigenvalue_upper >= 0
        singular_bounds.append(isqrt(eigenvalue_upper * scale) + 1)
    singular_bounds = sorted(singular_bounds * 4, reverse=True)
    scale_root = isqrt(n * scale * scale) + 1

    def minimum_flips(width):
        trace_upper = scale_root * sum(singular_bounds[:width])
        gap = n * width * scale**2 - trace_upper
        return -((-gap) // (2 * scale**2))

    assert minimum_flips(n) == 1_437_068
    assert minimum_flips(n - 12) == 1_423_936
    print(f"t=599: trace bound requires {minimum_flips(n)} full-source flips or "
          f"{minimum_flips(n - 12)} after removing 12 columns")


def verify():
    s, q, tau = source_words()
    eligible = [ALL ^ ((q ^ rotate(q, d)) | (tau ^ rotate(tau, d)))
                for d in range(1, (LENGTH + 1) // 2)]

    def coefficients(value):
        return (4 * (mask.bit_count() - 2 * ((value ^ rotate(value, d)) & mask).bit_count())
                for d, mask in enumerate(eligible, 1))

    def proposed_coefficients():
        errors = {152: 16}
        for i in range(1, 19):
            errors[4 * i] = 64 * (-1)**i * (37 - 2 * i)
        for j in range(18):
            errors[82 + 4 * j] = 64 * (-1)**(17 + j) * (j + 1)
            errors[154 + 4 * j] = 64 * (-1)**(j + 1) * (18 - j)
        return [errors.get(d, 0) for d in range(1, (LENGTH + 1) // 2)]

    got = list(coefficients(s))
    assert got == proposed_coefficients()
    assert [(d, v) for d, v in enumerate(got, 1) if v % 64] == [(152, 16)]

    print("599: only residue failures modulo 64 are cyclic lags ±152 with coefficient +16")
    exact_repair_bounds([(d, value) for d, value in enumerate(got, 1) if value])


if __name__ == "__main__":
    verify()
