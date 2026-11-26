"""Exact exclusions for a one-spike splice of the T299 × Golay2 product."""

from itertools import combinations_with_replacement, product
from math import isqrt


def half_block_equations(length, cut):
    """Variables indicate membership in the group of the intact-block spike."""
    rhs = 1 << length
    cross = [0] * (length + 1)
    for left, right in product(range(cut), range(cut, length)):
        cross[right - left] ^= rhs | (1 << left) | (1 << right)
    for lag in range(1, length + 1):
        row = cross[lag] ^ cross[lag - 1]
        if lag > length - cut:
            row ^= 1 << (cut + lag - length - 1)
        if lag > cut:
            row ^= 1 << (length + cut - lag)
        yield row


def base_support_equations(length, group):
    """Variables choose between the two original classes within each group."""
    limit = (1 << length) - 1
    for lag in range(1, length):
        same_group = ~(group ^ (group >> lag)) & (limit >> lag)
        yield same_group ^ (same_group << lag) ^ ((same_group.bit_count() & 1) << length)
    # A selected class in each group may be chosen to have odd cardinality.
    yield group | (1 << length)
    yield (group ^ limit) | (1 << length)


def solve_binary(rows, variables):
    """Return the rank and a solution if consistent, or no solution."""
    pivots = {}
    limit = (1 << variables) - 1
    for row in rows:
        while coefficients := row & limit:
            pivot = coefficients.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
        else:
            if row:
                return None, None
    solution = 0
    for pivot, row in sorted(pivots.items()):
        digit = ((row >> variables) ^ (row & solution).bit_count()) & 1
        solution |= digit << pivot
    return len(pivots), solution


def satisfies(rows, variables, solution):
    return all(((row >> variables) ^ (row & solution).bit_count()) & 1 == 0 for row in rows)


def verify_lag_formula():
    """Compare the affine formula with direct cyclic overlap at small sizes."""
    for length in range(2, 8):
        for cut in range(1, length):
            rows = tuple(half_block_equations(length, cut))
            for group in range(1 << length):
                labels = [(group >> i) & 1 for i in range(length)]
                old = [2 * block + label for block in (0, 1) for label in labels]
                words = old[:cut] + [3] + old[cut:]
                for lag, row in enumerate(rows, 1):
                    direct = sum(value == words[(i + lag) % len(words)]
                                 for i, value in enumerate(words)) & 1
                    assert direct == (((row & group).bit_count() ^ (row >> length)) & 1)


def verify_adjacent_twins():
    """Check the adjacent-twin support obstruction directly at small sizes."""
    for length in range(2, 8):
        for group in range(1, (1 << length) - 1):
            labels = [(group >> i) & 1 for i in range(length)]
            old = [2 * block + label for label in labels for block in (0, 1)]
            for cut, spike in product(range(2 * length + 1), range(4)):
                words = old[:cut] + [spike] + old[cut:]
                assert any(sum(value == words[(i + lag) % len(words)]
                               for i, value in enumerate(words)) & 1
                           for lag in range(1, length + 1))


def verify_totals():
    tails = [
        trail for trail in combinations_with_replacement(range(isqrt(598) + 1), 3)
        if sum(value * value for value in trail) == 598
    ]
    assert tails == [(6, 11, 21), (7, 15, 18)]
    base_totals = []
    for trail in tails:
        even, = (value for value in trail if value % 2 == 0)
        low, high = (value for value in trail if value % 2)
        base_totals.append((even // 2, even // 2, (high - low) // 2, (high + low) // 2))
    assert base_totals == [(3, 3, 5, 16), (9, 9, 4, 11)]


def verify_support_sieve():
    length = 299
    first_pass, second_pass = [], []
    alternating = sum(1 << index for index in range(0, length, 2))
    for cut in range(1, length):
        rows = tuple(half_block_equations(length, cut))
        rank, group = solve_binary(rows, length)
        if group is None:
            continue
        assert rank == length and satisfies(rows, length, group)
        first_pass.append(cut)

        rows = tuple(base_support_equations(length, group))
        rank, split = solve_binary(rows, length)
        if split is None:
            continue
        assert rank == 150 and satisfies(rows, length, split)
        assert group == alternating
        second_pass.append(cut)
    assert first_pass == [cut for cut in range(1, length) if cut % 3 != 1]
    assert second_pass == [149, 150]
    print("Golay2 half-block: 198/298 cuts survive pair membership; only cuts 149, 150 survive base support")


def sign_row(terms, variables):
    """Encode sum(c · (-1)^u) = 0 modulo 4; u is a mask of sign bits."""
    constant, row = 0, 0
    for coefficient, exponent in terms:
        constant += coefficient
        row ^= exponent
    assert constant % 2 == 0
    return row | (((constant // 2) & 1) << variables)


def central_sign_equations(half_length):
    """Equations modulo 4 after imposing the central skew-word condition."""
    length = 4 * half_length - 1
    letters = [(1, 1 << i) for i in range(length)]
    left_skew = [(1, 1 << (length + i)) for i in range(half_length)]
    skew = left_skew + [(-coefficient, exponent) for coefficient, exponent in reversed(left_skew)]
    last = [(1, 1 << (length + half_length + i)) for i in range(2 * half_length - 1)]
    even, odd = letters[::2], letters[1::2]
    variables = length + len(left_skew) + len(last)

    norm_rows = []
    for lag in range(1, 2 * half_length):
        terms = [(x * y, a ^ b) for word in (even, odd, skew, last)
                 for (x, a), (y, b) in zip(word, word[lag:])]
        norm_rows.append(sign_row(terms, variables))

    splice_rows = []
    for lag in range(1, 2 * half_length):
        terms = []
        for word, cut in ((even, half_length), (odd, half_length - 1)):
            for i in range(max(0, cut - lag), min(cut, len(word) - lag)):
                x, a = word[i]
                y, b = word[i + lag]
                terms.append((x * y, a ^ b))
        if lag >= half_length:
            coefficient, exponent = left_skew[lag - half_length]
            terms.append((coefficient, exponent))
        splice_rows.append(sign_row(terms, variables))
    return norm_rows + splice_rows, variables


def verify_norm_rows(rows, variables, half_length):
    """Check the affine rows against raw signed aperiodic coefficients."""
    from random import Random

    rng = Random(599)
    length = 4 * half_length - 1
    for _ in range(8):
        assignment = rng.getrandbits(variables)
        signs = [1 - 2 * ((assignment >> i) & 1) for i in range(variables)]
        split, skew, last = signs[:length], signs[length:length + half_length], signs[length + half_length:]
        intact = skew + [-value for value in reversed(skew)]
        words = split[::2], split[1::2], intact, last
        for lag, row in enumerate(rows, 1):
            coefficient = sum(a * b for word in words
                              for a, b in zip(word, word[lag:]))
            assert coefficient % 2 == 0
            actual = ((row >> variables) ^ (row & assignment).bit_count()) & 1
            assert actual == (coefficient // 2) % 2


def verify_central_obstruction():
    half_length = 75
    rows, variables = central_sign_equations(half_length)
    assert variables == 523 and len(rows) == 298
    rank, signs = solve_binary(rows, variables)
    assert rank == 298 and signs is not None and satisfies(rows, variables, signs)
    norm_rows = rows[:2 * half_length - 1]
    verify_norm_rows(norm_rows, variables, half_length)
    rhs = 1 << variables
    for index in range(half_length):
        mirror = 2 * half_length - 1 - index
        # The system forces equal endpoints and opposite interior signs.
        opposite_claim = (1 << (2 * index)) | (1 << (2 * mirror))
        if index == 0:
            opposite_claim |= rhs
        _, counterexample = solve_binary(norm_rows + [opposite_claim], variables)
        assert counterexample is None
    remainder = 598 - 2**2
    assert remainder % 11 == 0 and remainder % 121 != 0
    assert all((a*a + b*b) % 11 != 0 for a, b in product(range(11), repeat=2) if a or b)
    print("Golay2 central cuts: split-even sum forced to ±2; remaining two squares cannot sum to 594")


def verify():
    verify_lag_formula()
    verify_adjacent_twins()
    verify_totals()
    verify_support_sieve()
    verify_central_obstruction()


if __name__ == "__main__":
    verify()
