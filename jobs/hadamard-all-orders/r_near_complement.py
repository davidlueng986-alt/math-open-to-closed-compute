"""Check the finite-field units used in the near-complement cycle obstruction."""

from math import isqrt

from verify import require


TRACE = -1196
POINTS = 1198
CYCLE_TESTS = ((3, 5), (3, 239), (7, 223), (19, 113), (21, 83), (57, 468653), (133, 1063))


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def power_of_root(exponent, modulus):
    """Coordinates in the basis 1,z, with z² = TRACE·z − 1."""
    a, b = 1, 0
    for _ in range(exponent):
        a, b = -b % modulus, (a + TRACE * b) % modulus
    return a, b


def check_cycle_tests():
    discriminant = TRACE**2 - 4
    for order, q in CYCLE_TESTS:
        require(prime(q) and q % 2 and POINTS % q, f"admissible field at {q}")
        require(pow(discriminant, (q - 1) // 2, q) == q - 1, f"irreducible quadratic at {q}")
        require(power_of_root(order, q) == (1, 0), f"root period {order} at {q}")
        require(all(power_of_root(order // d, q) != (1, 0)
                    for d in range(2, order + 1) if order % d == 0 and prime(d)),
                f"exact period {order} at {q}")
        require(power_of_root(order, q*q) != (1, 0), f"simple lifting valuation at {q}")

    # With one isolated point, equal cycle lengths must divide 1197. The
    # number of cycles is odd. A certified test contradicts each such length.
    remaining = POINTS - 1
    lengths = [d for d in range(2, remaining + 1) if remaining % d == 0]
    for length in lengths:
        require((remaining // length) % 2 == 1, "odd number of equal cycles")
        require(any(length % order == 0 and length % q != 0 for order, q in CYCLE_TESTS),
                f"obstruction for equal length {length}")
    print(f"n=2396: {len(CYCLE_TESTS)} verified finite-field cycle tests; all {len(lengths)} equal-length models excluded")


if __name__ == '__main__':
    check_cycle_tests()
