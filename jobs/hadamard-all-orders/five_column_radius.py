"""Exact Hamming-radius bounds for the 1,193-column exterior stack."""

from collections import Counter, defaultdict
from itertools import combinations
from math import comb

from five_column_constraints import BOTTOM, LOWER_OMISSIONS, TOP, exterior_sources
from verify import require, rows_from_columns


RADIUS, MODULUS = 24, 299
ROW_PAIRS = ((4, 13), (4, 15), (2, 5), (2, 6), (7, 14), (7, 16), (9, 10))


def column_signs(word, length):
    return [2 * (word >> i & 1) - 1 for i in range(length)]


def forced_positions(omitted_rows):
    # At a lower nonborder row, the number of positive new signs is the
    # number of positive omitted signs minus one.
    fixed = {0: 0}
    for i, pattern in enumerate(omitted_rows[1:], 1):
        if pattern.bit_count() in (1, 6):
            fixed[i] = int(pattern.bit_count() == 6)
    return fixed


def mismatches(word, forced):
    return [i for i, bit in forced.items() if word >> i & 1 != bit]


def check_pairing_independent(upper_patterns, omitted_lower, lower_patterns, forced):
    require(Counter(upper_patterns) == {1: 299, 3: 299, 5: 299, 7: 299},
            "balanced upper omitted sign cube")
    cutoff = 2 * BOTTOM * RADIUS // TOP
    require(4 * BOTTOM * RADIUS < 299 * TOP, "projection energy below the upper sign-cube gap")
    compatible = [f for f in range(cutoff + 1) if TOP * f - 3 * f * f <= BOTTOM * RADIUS]
    top_radius = max(compatible)
    require(top_radius == 25, "bound on the upper Hamming distance")

    # Near the lower constant column, the only possible lower word has all
    # 24 mandatory changes. Balance forces 22 changes in the upper constant.
    lower_flips = mismatches(omitted_lower[0], forced)
    require(len(lower_flips) == RADIUS and omitted_lower[0] == 0, "unique lower constant candidate")
    moments = [-sum(2 * (col >> i & 1) - 1 for i in lower_flips) for col in omitted_lower]
    lower_energy = BOTTOM * RADIUS - sum(value * value for value in moments)
    energies = set()
    changes = RADIUS - 2
    for a, b, c in combinations(range(changes + 3), 3):
        counts = (a, b - a - 1, c - b - 1, changes + 2 - c)
        projections = [sum(count * (2 * (pattern >> j & 1) - 1)
                           for count, pattern in zip(counts, (1, 3, 5, 7), strict=True)) for j in range(3)]
        energies.add(TOP * changes - sum(value * value for value in projections))
    gap = min(abs(value - lower_energy) for value in energies)
    require(gap == 92, "constant role excluded by Parseval and balance")

    near_roles = [j for j, col in enumerate(omitted_lower[1:], 1) if len(mismatches(col, forced)) <= RADIUS]
    require([LOWER_OMISSIONS[j] for j in near_roles] == [1013, 1108], "two nonconstant roles survive forced rows")
    for col in omitted_lower:
        require(len(mismatches(col ^ ((1 << BOTTOM) - 1), forced)) > RADIUS,
                "opposite signs fail the forced rows")
    for j in near_roles:
        conflicts = sum((pattern.bit_count() == 2 and pattern >> j & 1)
                        or (pattern.bit_count() == 5 and not (pattern >> j & 1))
                        for pattern in lower_patterns[1:])
        budget = RADIUS - len(mismatches(omitted_lower[j], forced))
        require(conflicts == 113 and conflicts > 2 * budget, "no repeat near a lower omission")

    require(TOP - 4 * top_radius > 4 * RADIUS, "two distinct lower roles need different upper roles")
    error_limit = 2 * (top_radius + RADIUS)
    upper_energy = 3 * (BOTTOM * BOTTOM - TOP * TOP) + 2 * error_limit * 6 * TOP
    lower_energy_times_three = 4 * (BOTTOM - 2 - 4 * RADIUS) ** 2
    require((upper_energy, lower_energy_times_three) == (1435248, 4857616), "exact norm bounds")
    require(lower_energy_times_three > 3 * upper_energy, "two close columns are impossible")
    print("any retained pairing: at least four new lower columns have distance at least 25 from every signed omission")
    print(f"  lower constant projection-energy gap / 4 = {gap}; two-column norm contradiction gap × 3 = "
          f"{lower_energy_times_three - 3 * upper_energy}")


def small_signatures(rows, limit, dimension):
    yield (), (0,) * dimension
    if limit >= 1:
        for i, value in enumerate(rows):
            yield (i,), value
    if limit >= 2:
        for i, u in enumerate(rows):
            for j in range(i + 1, len(rows)):
                yield (i, j), tuple((a + b) % MODULUS for a, b in zip(u, rows[j], strict=True))


def compatible_subset(rows, target, budget):
    if budget == 0:
        return not any(target)
    # Index on four coordinates, then verify all coordinates for every hit.
    # The prefix reduces work without dropping any possible solution.
    prefix_size = 4
    prefixes = [row[:prefix_size] for row in rows]
    wanted = target[:prefix_size]
    left = defaultdict(list)
    for indices, signature in small_signatures(prefixes, budget // 2, prefix_size):
        left[signature].append(indices)
    for indices, signature in small_signatures(prefixes, budget - budget // 2, prefix_size):
        complement = tuple((a - b) % MODULUS for a, b in zip(wanted, signature, strict=True))
        for other in left.get(complement, ()):
            if not any(i in other for i in indices) and all(
                sum(rows[i][j] for i in indices + other) % MODULUS == value
                for j, value in enumerate(target)
            ):
                return True
    return False


def check_indexed_pairing(upper, lower, omitted_lower, upper_patterns, forced):
    upper_rows = rows_from_columns(TOP, upper[3:])
    lower_rows = rows_from_columns(BOTTOM, [col for j, col in enumerate(lower) if j not in LOWER_OMISSIONS])
    require(all(upper_patterns[a] == upper_patterns[b] for a, b in ROW_PAIRS), "matching omitted upper types")
    differences = [tuple(((upper_rows[b] ^ col).bit_count() - (upper_rows[a] ^ col).bit_count()) % MODULUS
                         for a, b in ROW_PAIRS) for col in lower_rows]
    free_rows = [i for i in range(BOTTOM) if i not in forced]
    require(len(free_rows) == 1034, "optional lower positions")
    total = 0
    for j, initial in enumerate(omitted_lower):
        changes = mismatches(initial, forced)
        budget = RADIUS - len(changes)
        if budget < 0:
            continue
        require(budget <= 4, "meet-in-the-middle handles all available flips")
        signs = column_signs(initial, BOTTOM)
        target = tuple(-sum(signs[i] * differences[i][p] for i in changes) % MODULUS
                       for p in range(len(ROW_PAIRS)))
        possible = [tuple(signs[i] * value % MODULUS for value in differences[i]) for i in free_rows]
        require(not compatible_subset(possible, target, budget), "all modular signatures rejected")
        count = sum(comb(len(free_rows), k) for k in range(budget + 1))
        total += count
        print(f"  indexed pairing, lower column {LOWER_OMISSIONS[j]}: {count:,} candidates excluded")
    require(total == 95074609413, "exact indexed radius cardinality")
    print(f"indexed pairing: none of {total:,} words within radius 24 can be an added lower column")


def main():
    upper, lower = exterior_sources()
    omitted_lower = [lower[j] for j in LOWER_OMISSIONS]
    upper_patterns = rows_from_columns(TOP, upper[:3])
    lower_patterns = rows_from_columns(BOTTOM, omitted_lower)
    forced = forced_positions(lower_patterns)
    require(len(forced) == 166, "forced lower signs including the border")
    check_pairing_independent(upper_patterns, omitted_lower, lower_patterns, forced)
    check_indexed_pairing(upper, lower, omitted_lower, upper_patterns, forced)


if __name__ == '__main__':
    main()
