"""Verify the finite-field and integer determinant obstructions for the partner graph."""

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


def path_and_cycle_determinants(modulus):
    diagonal = POINTS - 2
    path = [0, 1]
    for _ in range(POINTS - 1):
        path.append((diagonal * path[-1] - path[-2]) % modulus)
    # For length two the off-diagonal entries of the cycle are both 2.
    cycle = [0] + [(path[length + 1] - path[length - 1]
                    - 2 * (-1)**length) % modulus for length in range(1, POINTS)]
    return path, cycle


def check_figure_eights():
    candidates = []
    for even in range(2, POINTS - 1, 2):
        for odd in range(3, POINTS - even, 2):
            remaining = POINTS - 1 - even - odd
            # The ordinary cycles all have even length, and digons are allowed.
            for parity in ((0, 1) if remaining >= 4 else (remaining // 2,)):
                candidates.append((even, odd, parity))
    initial_count = len(candidates)
    require(initial_count == 355813, "enumeration of all relaxed figure-eight models")
    for modulus in range(3, 152, 2):
        if not prime(modulus):
            continue
        path, cycle = path_and_cycle_determinants(modulus)
        factor = POINTS * (POINTS - 4) % modulus
        square_residues = {value * value % modulus for value in range(modulus)}
        survivors = []
        for even, odd, parity in candidates:
            figure = (cycle[even] * path[odd] + cycle[odd] * path[even]
                      - POINTS * path[even] * path[odd])
            if figure * (factor if parity else 1) % modulus in square_residues:
                survivors.append((even, odd, parity))
        candidates = survivors
    require(not candidates, f"square determinant survivors: {candidates}")
    print(f"n=2396: all {initial_count:,} figure-eight models fail the square determinant condition "
          "at an odd prime at most 151")


if __name__ == "__main__":
    check_cycle_tests()
    check_figure_eights()
