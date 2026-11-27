"""Transparent exact CNF for k mutually orthogonal Latin squares of order n.

The builder supplies var(hashable_key) -> positive int and add(iterable[int]).
The encoding uses one-hot square entries and Latin row-composition channels.
It is a reference formulation; MOLS10-3 also has the preserved smaller E077
six-shard encoding. No relation, automorphism, or subsquare hypothesis is used.
"""

from itertools import combinations
from math import comb


def counts(n, k, normalize=True):
    if not isinstance(n, int) or not isinstance(k, int) or n < 2 or k < 1:
        raise ValueError("Require integer n >= 2 and k >= 1")
    arrays = k + comb(k, 2)
    return {
        "primary_variables": k * n**3,
        "auxiliary_variables": comb(k, 2) * n**3,
        "variables": arrays * n**3,
        "clauses": 3 * arrays * n*n * (1 + comb(n, 2))
        + comb(k, 2) * n**4 + (k*n+n-1 if normalize else 0),
    }


def _exactly_one(builder, values):
    values = list(values)
    builder.add(values)
    for a, b in combinations(values, 2):
        builder.add((-a, -b))


def _latin(builder, grid, n):
    for r in range(n):
        for c in range(n):
            _exactly_one(builder, (grid[r][c][s] for s in range(n)))
    for r in range(n):
        for s in range(n):
            _exactly_one(builder, (grid[r][c][s] for c in range(n)))
    for c in range(n):
        for s in range(n):
            _exactly_one(builder, (grid[r][c][s] for r in range(n)))


def emit(builder, n, k, normalize=True):
    """Emit the exact formula and return deterministic decoding metadata."""
    size = counts(n, k, normalize)
    x = [[[[builder.var(("x", t, r, c, s)) for s in range(n)]
            for c in range(n)] for r in range(n)] for t in range(k)]
    for grid in x:
        _latin(builder, grid, n)
    for a, b in combinations(range(k), 2):
        y = [[[builder.var(("y", a, b, r, u, v)) for v in range(n)]
              for u in range(n)] for r in range(n)]
        _latin(builder, y, n)
        for r in range(n):
            for c in range(n):
                for u in range(n):
                    for v in range(n):
                        builder.add((-x[a][r][c][u], -x[b][r][c][v], y[r][u][v]))
    if normalize:
        for t in range(k):
            for c in range(n):
                builder.add((x[t][0][c][c],))
        for r in range(1, n):
            builder.add((x[0][r][0][r],))
    return {
        "kind": "mols", "encoding": "mols-reference-composition-v1",
        "n": n, "k": k, "normalized": bool(normalize),
        "primary_variables": [x[t][r][c][s] for t in range(k)
                              for r in range(n) for c in range(n) for s in range(n)],
        "expected_variables": size["variables"],
        "expected_clauses": size["clauses"],
        "normalization": "first row of every square; first column of square 0" if normalize else "none",
    }


def verify(squares, n=None, k=None):
    """Check the original Latin and pairwise orthogonality conditions directly."""
    errors = []
    try:
        if k is None:
            k = len(squares)
        if n is None:
            n = len(squares[0])
        if n < 2 or k < 1 or len(squares) != k:
            raise ValueError("wrong number of squares or invalid order")
        symbols = set(range(n))
        for t, square in enumerate(squares):
            if len(square) != n or any(len(row) != n for row in square):
                raise ValueError(f"square {t}: wrong dimensions")
            if any(type(v) is not int or v not in symbols for row in square for v in row):
                raise ValueError(f"square {t}: invalid symbol")
            for r in range(n):
                if set(square[r]) != symbols:
                    errors.append(f"square {t}, row {r}: not a permutation")
            for c in range(n):
                if {square[r][c] for r in range(n)} != symbols:
                    errors.append(f"square {t}, column {c}: not a permutation")
        for a, b in combinations(range(k), 2):
            pairs = {(squares[a][r][c], squares[b][r][c])
                     for r in range(n) for c in range(n)}
            if len(pairs) != n*n:
                errors.append(f"squares {a},{b}: only {len(pairs)} distinct ordered pairs")
    except (TypeError, ValueError, IndexError) as exc:
        errors.append(str(exc))
    return {"valid": not errors, "n": n, "k": k, "errors": errors}


def normalize(squares):
    """Apply only the two globally safe normalizations used by emit."""
    checked = verify(squares)
    if not checked["valid"]:
        raise ValueError(checked["errors"])
    n = checked["n"]
    # Symbol relabelings are independent between squares.
    result = []
    for square in squares:
        labels = {square[0][c]: c for c in range(n)}
        result.append([[labels[v] for v in row] for row in square])
    # A common row permutation fixes row zero and makes column zero of L0 identity.
    row_for = {result[0][r][0]: r for r in range(n)}
    return [[list(square[row_for[r]]) for r in range(n)] for square in result]


def decode(model, metadata):
    """Decode primary entries; missing or ambiguous entries are rejected."""
    positive = {int(v) for v in model if int(v) > 0}
    n, k = metadata["n"], metadata["k"]
    ids = metadata["primary_variables"]
    if len(ids) != k*n**3:
        raise ValueError("wrong primary variable map length")
    squares = []
    for t in range(k):
        square = []
        for r in range(n):
            row = []
            for c in range(n):
                offset = ((t*n+r)*n+c)*n
                values = [s for s in range(n) if ids[offset+s] in positive]
                if len(values) != 1:
                    raise ValueError(f"ambiguous or missing value at {t},{r},{c}")
                row.append(values[0])
            square.append(row)
        squares.append(square)
    checked = verify(squares, n, k)
    if not checked["valid"]:
        raise ValueError(checked["errors"])
    return squares


def witness_assignment(squares, builder):
    """Construct x/y truth values from a valid witness, for semantic controls."""
    checked = verify(squares)
    if not checked["valid"]:
        raise ValueError(checked["errors"])
    n, k = checked["n"], checked["k"]
    assignment = []
    for t in range(k):
        for r in range(n):
            for c in range(n):
                for s in range(n):
                    v = builder.var(("x", t, r, c, s))
                    assignment.append(v if squares[t][r][c] == s else -v)
    for a, b in combinations(range(k), 2):
        for r in range(n):
            inverse = {squares[a][r][c]: c for c in range(n)}
            for u in range(n):
                value = squares[b][r][inverse[u]]
                for v in range(n):
                    var = builder.var(("y", a, b, r, u, v))
                    assignment.append(var if v == value else -var)
    return assignment
