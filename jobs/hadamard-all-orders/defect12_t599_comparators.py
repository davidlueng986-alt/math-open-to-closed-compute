"""Check the 149 symmetric two-hole comparators for half-flip sources at 599."""

from collections import Counter
from itertools import combinations


HALF_LENGTH = 299
MIDPOINT = HALF_LENGTH // 2
LAST = HALF_LENGTH - 1
FULL = (1 << HALF_LENGTH) - 1

# Preorder certificate for h=1. Internal labels are zero-based variable
# indices after linear reduction. Each -1 must reduce to a contradiction.
H1_TREE = (
    0, 2, 0, 0, 1, -1, -1, 0, 3, 3, 0, -1, -1, 0, -1, -1, 3, 0, -1, -1,
    1, -1, -1, -1, 0, 1, -1, -1, 0, -1, -1, 1, 3, 1, 0, -1, 0, -1, -1, 5,
    5, 1, -1, -1, 1, -1, -1, 5, 1, 0, -1, -1, -1, 2, -1, -1, 1, -1, 0, 0,
    -1, -1, 0, -1, 0, -1, -1, 3, 6, 5, 4, -1, -1, 0, -1, 0, -1, -1, 5, 0,
    -1, -1, 0, -1, -1, -1, 2, 1, 3, -1, 6, 5, 0, 0, -1, -1, -1, 4, -1, -1,
    5, 0, -1, -1, 0, -1, -1, 3, 1, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, 1,
    5, 5, 2, -1, -1, 1, -1, 0, -1, -1, 5, 1, -1, -1, 1, -1, -1, 0, 0, -1,
    -1, -1, 0, 0, 0, -1, -1, 1, -1, -1, 0, 0, 3, 3, 1, -1, -1, 0, -1, -1,
    3, 0, -1, -1, 0, -1, -1, -1, 1, -1, -1,
)


def bit_indices(word):
    while word:
        bit = word & -word
        yield bit.bit_length() - 1
        word ^= bit


def eliminate(rows):
    pivots = {}
    for word, value in rows:
        while word:
            j = word.bit_length() - 1
            if j not in pivots:
                pivots[j] = (word, value)
                break
            previous, constant = pivots[j]
            word ^= previous
            value ^= constant
        else:
            if value:
                return None
    return sorted(pivots.items())


def assignment(pivots, free=0, homogeneous=False):
    values = free
    for j, (row, constant) in pivots:
        target = 0 if homogeneous else constant
        if ((row & values).bit_count() & 1) != target:
            values ^= 1 << j
    return values


def reflection_system(supports):
    """An unknown records the parity difference across one reflection pair."""
    coordinates = [(support, j) for support in supports
                   for j in range(MIDPOINT) if (support >> j) & 1]
    assert len(coordinates) == 298
    for distance in range(1, HALF_LENGTH):
        active = {support: support & ((support << distance) ^ (support >> distance))
                  for support in supports}
        row = sum(((active[support] >> j) & 1) << i
                  for i, (support, j) in enumerate(coordinates))
        count = sum((support & (support >> distance)).bit_count() for support in supports)
        assert count % 2 == 0
        yield row, (count // 2) & 1


def mirror_system(supports, reflection):
    """Choose representative signs, then form the next linear lift."""
    reference = []
    reflection_words = []
    maps = []
    difference_index = orbit_index = 0
    for support in supports:
        signs = parity = 0
        coordinates = [None] * HALF_LENGTH
        for i in range(MIDPOINT + 1):
            if not ((support >> i) & 1):
                continue
            j = LAST - i
            coordinates[i] = coordinates[j] = orbit_index
            orbit_index += 1
            if i < j:
                if (reflection >> difference_index) & 1:
                    signs |= 1 << j
                    parity |= (1 << i) | (1 << j)
                difference_index += 1
        reference.append(signs)
        reflection_words.append(parity)
        maps.append(coordinates)
    assert difference_index == 298 and orbit_index == 300

    rows = []
    masks = []
    for distance in range(1, HALF_LENGTH):
        correlation = row = 0
        selected = tuple(support & (support >> distance) for support in supports)
        for mask, signs, parity, coordinates in zip(selected, reference, reflection_words, maps, strict=True):
            correlation += mask.bit_count() - 2 * (mask & (signs ^ (signs >> distance))).bit_count()
            # Count just one of each pair of reflected edges. Their
            # products agree exactly when their endpoint parities agree.
            left_of_reflection = (1 << ((HALF_LENGTH - distance) // 2)) - 1
            paired = mask & ~(parity ^ (parity >> distance)) & left_of_reflection
            for i in bit_indices(paired):
                row ^= (1 << coordinates[i]) ^ (1 << coordinates[i + distance])
        assert correlation % 4 == 0
        rows.append((row, (correlation // 4) & 1))
        masks.append(selected)

    # Independent global signs of the three nonsingleton classes do
    # not affect the correlation. Fix one mirror variable in each.
    rows.extend((1 << next(v for v in coordinates if v is not None), 0) for coordinates in maps)
    return rows, reference, maps, masks


def lift_is_consistent(reference, maps, masks, pivots, keep_polynomials=False):
    def expand(moves):
        return tuple(sum(1 << j for j, i in enumerate(coordinates)
                         if i is not None and ((moves >> i) & 1))
                     for coordinates in maps)

    initial = tuple(a ^ b for a, b in zip(reference, expand(assignment(pivots)), strict=True))
    fixed = {i for i, _ in pivots}
    free = [i for i in range(300) if i not in fixed]
    moves = [expand(assignment(pivots, 1 << i, homogeneous=True)) for i in free]
    counts = [sum(mask.bit_count() for mask in selected) for selected in masks]

    def residual(signs):
        result = 0
        for i, (selected, count) in enumerate(zip(masks, counts, strict=True)):
            distance = i + 1
            correlation = count - 2 * sum((mask & (word ^ (word >> distance))).bit_count()
                                          for mask, word in zip(selected, signs, strict=True))
            assert correlation % 8 == 0
            result |= ((correlation // 8) & 1) << i
        return result

    target = residual(initial)
    coefficient_columns = [target] if keep_polynomials else None
    columns = {}

    def reduce(word):
        while word:
            i = word.bit_length() - 1
            if i not in columns:
                break
            word ^= columns[i]
        return word

    def insert(word):
        reduced = reduce(word)
        if reduced:
            columns[reduced.bit_length() - 1] = reduced

    first_changes = []
    for move in moves:
        change = residual(tuple(a ^ b for a, b in zip(initial, move, strict=True))) ^ target
        first_changes.append(change)
        insert(change)
    if keep_polynomials:
        coefficient_columns.extend(first_changes)
    elif not reduce(target):
        return True, len(free), None
    for i, j in combinations(range(len(moves)), 2):
        signs = tuple(a ^ b ^ c for a, b, c in zip(initial, moves[i], moves[j], strict=True))
        change = residual(signs) ^ target ^ first_changes[i] ^ first_changes[j]
        insert(change)
        if keep_polynomials:
            coefficient_columns.append(change)
        elif not reduce(target):
            return True, len(free), None
    if not keep_polynomials:
        return False, len(free), None
    equations = [0] * LAST
    for j, coefficient in enumerate(coefficient_columns):
        for i in bit_indices(coefficient):
            equations[i] ^= 1 << j
    return not reduce(target), len(free), equations


def monomials(dimension, maximum_degree):
    return [sum(1 << i for i in subset) for degree in range(maximum_degree + 1)
            for subset in combinations(range(dimension), degree)]


def polynomial_pivots(equations, pivots=None):
    if pivots is None:
        pivots = {}
    for equation in equations:
        while equation:
            j = equation.bit_length() - 1
            if j not in pivots:
                if j == 0:
                    return None
                pivots[j] = equation
                break
            equation ^= pivots[j]
    return pivots


def substitute_linear_equations(equations, dimension):
    """Reduce the Boolean equations by the linear rows of their span."""
    dimensions = []
    while True:
        dimensions.append(dimension)
        pivots = polynomial_pivots(equations)
        if pivots is None:
            return None, dimensions
        linear = {j: row for j, row in pivots.items() if j <= dimension}
        if not linear:
            return list(pivots.values()), dimensions
        free = [j for j in range(1, dimension + 1) if j not in linear]
        new_monomials = {mask: i for i, mask in enumerate(monomials(len(free), 2))}
        substitutions = [1] + [0] * dimension
        for i, j in enumerate(free, 1):
            substitutions[j] = 1 << i
        for j, row in sorted(linear.items()):
            for i in bit_indices(row ^ (1 << j)):
                substitutions[j] ^= substitutions[i]

        def multiply(left, right):
            result = 0
            for i in bit_indices(left):
                a = 1 << (i - 1) if i else 0
                for j in bit_indices(right):
                    b = 1 << (j - 1) if j else 0
                    result ^= 1 << new_monomials[a | b]
            return result

        mapping = substitutions + [multiply(substitutions[i], substitutions[j])
                                   for i, j in combinations(range(1, dimension + 1), 2)]
        equations = []
        for row in pivots.values():
            result = 0
            for i in bit_indices(row):
                result ^= mapping[i]
            equations.append(result)
        dimension = len(free)


def cubic_lift(equations, dimension):
    quadratic = monomials(dimension, 2)
    cubic = {mask: i for i, mask in enumerate(monomials(dimension, 3))}
    pivots = polynomial_pivots(equations)
    assert pivots is not None
    basis = list(pivots.values())
    for variable in range(dimension):
        mapping = [1 << cubic[(1 << variable) | mask] for mask in quadratic]
        multiples = []
        for row in basis:
            result = 0
            for i in bit_indices(row):
                result ^= mapping[i]
            multiples.append(result)
        pivots = polynomial_pivots(multiples, pivots)
        if pivots is None:
            return variable + 1, ()
    return None, [row for j, row in pivots.items() if j <= dimension]


def fix_variable(equations, dimension, variable, value):
    """Substitute one Boolean value and renumber the remaining variables."""
    target = {mask: i for i, mask in enumerate(monomials(dimension - 1, 2))}
    bit = 1 << variable
    lower = bit - 1
    upper = ~((bit << 1) - 1)
    substitution = []
    for mask in monomials(dimension, 2):
        if mask & bit and not value:
            substitution.append(0)
        else:
            reduced_mask = (mask & lower) | ((mask & upper) >> 1)
            substitution.append(1 << target[reduced_mask])
    reduced = []
    for equation in equations:
        result = 0
        for i in bit_indices(equation):
            result ^= substitution[i]
        reduced.append(result)
    return reduced


def h1_contradiction(equations, dimension):
    """Check the cubic reduction at the root and all Boolean branches."""
    for expected in ([51, 50], [50, 48], [48, 47, 45]):
        equations, chain = substitute_linear_equations(equations, dimension)
        assert equations is not None and chain == expected
        dimension = chain[-1]
        if dimension != 45:
            contradiction, linear = cubic_lift(equations, dimension)
            assert contradiction is None and linear
            equations += linear

    branches = iter(H1_TREE)

    def check(rows, width, depth):
        variable = next(branches)
        rows, chain = substitute_linear_equations(rows, width)
        if variable == -1:
            assert rows is None
            return 1, depth
        width = chain[-1]
        assert rows is not None and 0 <= variable < width
        left = fix_variable(rows, width, variable, 0)
        right = fix_variable(rows, width, variable, 1)
        left_leaves, left_depth = check(left, width - 1, depth + 1)
        right_leaves, right_depth = check(right, width - 1, depth + 1)
        return left_leaves + right_leaves, max(left_depth, right_depth)

    leaves, depth = check(equations, dimension, 0)
    assert len(H1_TREE) == 2 * leaves - 1 and next(branches, None) is None
    return leaves, depth


def verify():
    outcomes = Counter()
    survivors = []
    for hole in range(MIDPOINT):
        pair = (1 << hole) | (1 << (LAST - hole))
        supports = (FULL, FULL ^ pair, pair)
        reflection_pivots = eliminate(reflection_system(supports))
        if reflection_pivots is None:
            outcomes["mod16"] += 1
            continue
        assert len(reflection_pivots) == 298
        equations, reference, coordinates, masks = mirror_system(supports, assignment(reflection_pivots))
        mirror_pivots = eliminate(equations)
        if mirror_pivots is None:
            outcomes["mod32"] += 1
            continue
        consistent, nullity, polynomials = lift_is_consistent(
            reference, coordinates, masks, mirror_pivots, keep_polynomials=hole in (1, 2, 37, 99))
        if not consistent:
            outcomes["mod64 linearization"] += 1
            continue
        if hole == 1:
            assert h1_contradiction(polynomials, nullity) == (86, 9)
            outcomes["mod64 Boolean branching"] += 1
            continue
        if hole == 2:
            reduced, dimensions = substitute_linear_equations(polynomials, nullity)
            assert reduced is None and dimensions == [32, 30, 28, 27, 26, 24]
            outcomes["mod64 linear substitution"] += 1
            continue
        if hole == 37:
            assert cubic_lift(polynomials, nullity) == (33, ())
            outcomes["mod64 cubic"] += 1
            continue
        if hole == 99:
            contradiction, linear = cubic_lift(polynomials, nullity)
            assert contradiction is None and len(linear) == 1
            reduced, dimensions = substitute_linear_equations(polynomials + linear, nullity)
            assert reduced is not None and dimensions == [51, 50]
            assert cubic_lift(reduced, dimensions[-1]) == (33, ())
            outcomes["mod64 cubic and substitution"] += 1
            continue
        survivors.append((hole, nullity))

    assert outcomes == {"mod16": 17, "mod32": 16, "mod64 linearization": 110,
                        "mod64 linear substitution": 1, "mod64 cubic": 1,
                        "mod64 cubic and substitution": 1, "mod64 Boolean branching": 1}
    assert survivors == [(0, 149), (74, 75)]
    print("t=599 comparators: 17 fail mod16, 16 more fail mod32, 110 more fail the mod64 linearization")
    print("Boolean lift: h=2,37,99 fail by linear substitution, cubic lifting, or both")
    print("Boolean lift: h=1 has 86 contradictory leaves at maximum branch depth 9")
    print("surviving hole indices and normalized residual nullities:", survivors)


if __name__ == "__main__":
    verify()
