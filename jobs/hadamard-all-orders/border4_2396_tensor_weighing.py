"""Exact width-four exclusions for tensor repeats and independent weighing words."""

from itertools import combinations, product

from border4_2396_paley_split import square_profiles

TEST_VECTORS = {
    13: (100, 89, 57, 12, -35, -75, -97, -97, -75, -35, 12, 57, 89),
    23: (100, 96, 85, 68, 46, 20, -7, -33, -58, -78, -92, -99,
         -99, -92, -78, -58, -33, -7, 20, 46, 68, 85, 96),
}


def rayleigh_census(length, word_sum, bound):
    """Every tested word has a certificate for an eigenvalue greater than bound."""
    half = length // 2
    vec = TEST_VECTORS[length]
    weights = tuple(sum(x * vec[(i + d) % length] for i, x in enumerate(vec))
                    for d in range(length))
    # Each permutation j -> k*j defines another integer test vector.
    probes = tuple(tuple(weights[(k * d) % length] for d in range(1, half + 1))
                   for k in range(1, half + 1))
    cutoff = (bound - length) * weights[0]
    limit = (1 << length) - 1
    required = (length - word_sum) // 2
    cache = set()
    representatives = 0
    # A nonempty negative set may be rotated to contain 0. Negation lets us
    # assume the sequence sum is the given positive representative.
    for others in combinations(range(1, length), required - 1):
        representatives += 1
        mask = 1 | sum(1 << value for value in others)
        rotations = (((mask << lag) & limit) | (mask >> (length - lag))
                     for lag in range(1, half + 1))
        correlations = tuple(length - 2 * (mask ^ shifted).bit_count() for shifted in rotations)
        if correlations in cache:
            continue
        cache.add(correlations)
        assert any(2 * sum(a * b for a, b in zip(correlations, row, strict=True)) > cutoff
                   for row in probes), (mask, correlations)
    return representatives, len(cache)


def verify_tensor():
    # A product W=u⊗v is the repeated word. Quotient diagonal bounds
    # are 2*13*v(1)^2, 2*23*u(1)^2 <= 1196.
    allowed = [x for x in range(1, 24, 2) if 2 * 13 * x**2 <= 1196]
    allowed_other = [x for x in range(1, 14, 2) if 2 * 23 * x**2 <= 1196]
    assert allowed == allowed_other == [1, 3, 5]
    profiles = sorted((a, b) for a, b in product(allowed, allowed_other) if a * b in (7, 11, 15, 21))
    assert profiles == [(3, 5), (5, 3)]

    # Sum-3 on length 23: the nonzero lags are c == -1 (mod 4), so
    # c*c >= 2*c+3. Parseval bounds the maximum nontrivial Fourier power.
    length, squared_sum = 23, 3**2
    off_square_lower = 2 * (squared_sum - length) + 3 * (length - 1)
    moment_lower = length * (length**2 + off_square_lower) - squared_sum**2
    moment_one = length**2 - squared_sum
    assert moment_lower == 12960 and moment_one == 520
    assert 5**2 * moment_lower > 598 * moment_one

    c13 = rayleigh_census(13, 3, 20)
    c23 = rayleigh_census(23, 5, 30)
    assert c13 == (495, 57) and c23 == (319770, 17105)
    assert 20 * 30 > 598
    print("Tensor W excluded by exact integer Rayleigh bounds.")


def verify_weighing():
    profiles = []
    for profile in square_profiles(599, 4):
        if max(profile) > 17:
            continue
        even = [value for value in profile if value % 2 == 0]
        if len(even) == 1 and even[0] % 4 == 2:
            profiles.append(profile)
    assert profiles == [(2, 9, 15, 17), (3, 13, 14, 15), (6, 7, 15, 17), (6, 13, 13, 15), (7, 10, 15, 15)]
    assert all(15 in profile for profile in profiles)

    multiplier = 27
    assert pow(3, 3, 299) == pow(5, 4, 299) == multiplier
    assert multiplier % 13 == 1 and multiplier % 23 != 1
    assert pow(multiplier, 11, 23) == 1
    absolute_values = {abs(a + 11 * (b + c)) for a, b, c in product((-1, 0, 1), repeat=3)}
    assert {value for value in absolute_values if value**2 <= 225} == {0, 1, 10, 11, 12}
    profiles = [
        (ones, tens, elevens, twelves)
        for ones in range(14)
        for tens, elevens, twelves in product(range(3), repeat=3)
        if ones + tens + elevens + twelves <= 13
        and ones + 100 * tens + 121 * elevens + 144 * twelves == 225
    ]
    assert profiles == [(4, 1, 1, 0)]
    assert all(abs(10 * a + 11 * b + units) != 15
               for a, b, units in product((-1, 1), (-1, 1), (-4, -2, 0, 2, 4)))
    print("Independent perfect T rows excluded by the order-eleven weighing constraint.")


if __name__ == "__main__":
    verify_tensor()
    verify_weighing()
