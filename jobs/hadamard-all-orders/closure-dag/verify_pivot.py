"""Replay the pivot-to-clique correspondence on exact Paley examples."""

from collections import defaultdict
from itertools import combinations
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import check_marginals, paley, require, verify_orthogonal


def rows(word, size):
    return [row for row in range(size) if word >> row & 1]


def restrict(word, selected_rows):
    return sum(1 << new for new, old in enumerate(selected_rows) if word >> old & 1)


def scatter(word, selected_rows):
    return sum(1 << old for new, old in enumerate(selected_rows) if word >> new & 1)


def intersections(columns, mask):
    return tuple((column & mask).bit_count() for column in columns)


def fixed_size_masks(size, weight):
    for support in combinations(range(size), weight):
        yield sum(1 << row for row in support)


def pivot_matrices(t, y, pivot):
    b = 2 * t - 1
    mask = (1 << b) - 1
    row_count = 2 * b
    positive_rows = rows(y[pivot], row_count)
    negative_rows = rows(y[pivot] ^ ((1 << row_count) - 1), row_count)
    other = [i for i in range(len(y)) if i != pivot]
    a = [restrict(y[i], positive_rows) for i in other]
    b_matrix = [mask ^ restrict(y[i], negative_rows) for i in other]
    require(len(positive_rows) == len(negative_rows) == len(other) == b, "pivot dimensions")

    for matrix in (a, b_matrix):
        require(all(word.bit_count() == t - 1 for word in matrix), "pivot column regularity")
        require(all(sum(word >> row & 1 for word in matrix) == t - 1
                    for row in range(b)), "pivot row regularity")
    for i in range(b):
        for j in range(i + 1):
            gram = (a[i] & a[j]).bit_count() + (b_matrix[i] & b_matrix[j]).bit_count()
            require(gram == (t - 2) + (t if i == j else 0), "pivot Gram identity")

    reconstructed = [scatter(left, positive_rows) | scatter(right ^ mask, negative_rows)
                     for left, right in zip(a, b_matrix, strict=True)]
    reconstructed.insert(pivot, scatter(mask, positive_rows))
    require(reconstructed == y, "pivot inverse on original row labels")
    return a, b_matrix, positive_rows, negative_rows


def supports_intersect(vertex, other):
    u, v = vertex
    u_other, v_other = other
    return (u & u_other).bit_count() + (v & v_other).bit_count()


def exhaustive_order20(t, y, a, b, positive_rows, negative_rows):
    """Compare vertices and edges with the original incidence equations."""
    choices = tuple(fixed_size_masks(2 * t - 1, t - 1))
    right_by_signature = defaultdict(list)
    for v in choices:
        right_by_signature[intersections(b, v)].append(v)
    vertices = [(u, v) for u in choices for v in right_by_signature[intersections(a, u)]]
    reconstructed = [scatter(u, positive_rows) | scatter(v, negative_rows) for u, v in vertices]
    direct = {word for word in fixed_size_masks(4 * t - 2, 2 * t - 2)
              if all(count == t - 1 for count in intersections(y, word))}
    require(len(vertices) == len(direct) and set(reconstructed) == direct, "complete vertex inventory")
    edges = 0
    for i, j in combinations(range(len(vertices)), 2):
        adjacent = supports_intersect(vertices[i], vertices[j]) == t - 2
        require(adjacent == ((reconstructed[i] & reconstructed[j]).bit_count() == t - 2),
                "edge equivalence across the complete vertex inventory")
        edges += adjacent
    require(edges > 0, "edge control")
    return len(vertices), edges


def check_order(t):
    n = 4 * t
    columns = paley(n - 1)
    verify_orthogonal(n, columns)
    y = [word >> 2 for word in columns[1:] if not word & 2]
    x = [word >> 2 for word in columns[1:] if word & 2]
    check_marginals(t, y, x)
    require(len(x) == 2 * t - 1, "full clique width")
    require(all(intersections(y, word) == (t - 1,) * (2 * t) for word in x), "original mixed counts")
    for pivot in range(len(y)):
        a, b, positive_rows, negative_rows = pivot_matrices(t, y, pivot)
        vertices = [(restrict(word, positive_rows), restrict(word, negative_rows)) for word in x]
        for (u, v), word in zip(vertices, x, strict=True):
            require(u.bit_count() == v.bit_count() == t - 1, "selector sizes")
            require(intersections(a, u) == intersections(b, v), "selector signatures")
            require(scatter(u, positive_rows) | scatter(v, negative_rows) == word, "selector inverse")
        require(len(set(vertices)) == len(x), "distinct clique vertices")
        require(all(supports_intersect(left, right) == t - 2 for left, right in combinations(vertices, 2)),
                "full clique adjacency")
        if t == 5 and pivot == 0:
            count, edges = exhaustive_order20(t, y, a, b, positive_rows, negative_rows)
            print(f"n=20, pivot 0: all {count} valid vertices and {edges} edges match the incidence equations")
    print(f"n={n}: all {len(y)} pivots reconstruct the same design and a clique of size {len(x)}")


if __name__ == "__main__":
    for multiplier in (5, 11, 15):
        check_order(multiplier)
