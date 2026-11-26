"""Generate the exact independent-set obstruction CNF using only the standard library."""

import sys
from itertools import combinations
from pathlib import Path

from defect12_t599_near64 import LENGTH, rotate, source_words

LOWER_WITNESS = (0, 56, 75, 133, 153, 209, 229, 280, 299, 356, 375, 433, 452, 516)


def cyclic_distance(left, right, length):
    difference = (right - left) % length
    return min(difference, length - difference)


def forbidden_distances():
    s, q, tau = source_words()
    words = (s, s ^ tau, s ^ q, s ^ q ^ tau)
    inverse_four = pow(4, -1, LENGTH)
    distances = set()
    for displacement in range(1, LENGTH // 2 + 1):
        correlation = sum(
            LENGTH - 2 * (word ^ rotate(word, displacement)).bit_count()
            for word in words
        )
        if correlation:
            distances.add(cyclic_distance(0, inverse_four * displacement, LENGTH))

    assert distances == set(range(1, 19)) | {38} | set(range(244, 280))
    assert all(
        cyclic_distance(i, j, LENGTH) not in distances
        for i, j in combinations(LOWER_WITNESS, 2)
    )
    return sorted(distances)


def sequential_minimum(length, minimum):
    """Witness that at most length-minimum of the first variables are false.

    The state at (extra, count) means that the prefix of length extra+count
    already contains at least count false variables. Only the strip needed
    to prevent overflow is represented.
    """
    capacity = length - minimum
    variables = {}

    def state(extra, count):
        key = (extra, count)
        if key not in variables:
            variables[key] = length + len(variables) + 1
        return variables[key]

    for extra in range(minimum):
        for count in range(1, capacity + 1):
            prefix = extra + count
            current = state(extra, count)
            if count == 1:
                yield (prefix, current)
            else:
                yield (prefix, -state(extra, count - 1), current)
            if extra + 1 < minimum:
                yield (-current, state(extra + 1, count))
        yield (extra + capacity + 1, -state(extra, capacity))


def generate(output):
    forbidden = forbidden_distances()
    clauses = [
        (-(index + 1), -((index + distance) % LENGTH + 1))
        for index in range(LENGTH)
        for distance in forbidden
    ]
    clauses.append((1,))  # Rotate a nonempty hypothetical set to contain zero.
    clauses.extend(sequential_minimum(LENGTH, 15))
    variable_count = max(abs(lit) for clause in clauses for lit in clause)
    assert (variable_count, len(clauses)) == (9359, 49897)
    with output.open("w", encoding="ascii") as stream:
        stream.write(f"p cnf {variable_count} {len(clauses)}\n")
        for clause in clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    print("Wrote the 9359-variable exact CNF and checked the 14-column witness.")


if __name__ == "__main__":
    generate(Path(sys.argv[1]))
