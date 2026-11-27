"""Independent MOLS-to-projective-plane constructor and incidence checker.

This module does not consult a SAT assignment, CNF clauses, auxiliary channel
variables, solver status, or symmetry assumptions.  It checks the mathematical
object reconstructed from the primary Latin-square witness.
"""

from itertools import combinations


def check_complete_mols(squares):
    """Return n after checking n-1 pairwise orthogonal Latin squares of order n."""
    if not isinstance(squares, list) or not squares:
        raise ValueError("expected a nonempty list of Latin squares")
    n = len(squares[0])
    if n < 2 or len(squares) != n - 1:
        raise ValueError("a plane of order n requires exactly n-1 squares, n >= 2")
    symbols = set(range(n))
    for t, square in enumerate(squares):
        if len(square) != n or any(len(row) != n for row in square):
            raise ValueError(f"square {t}: incorrect dimensions")
        if any(type(v) is not int or not 0 <= v < n for row in square for v in row):
            raise ValueError(f"square {t}: symbols must be integers in [0,n)")
        if any(set(row) != symbols for row in square):
            raise ValueError(f"square {t}: non-Latin row")
        if any({square[r][c] for r in range(n)} != symbols for c in range(n)):
            raise ValueError(f"square {t}: non-Latin column")
    for a, b in combinations(range(n - 1), 2):
        pairs = {(squares[a][r][c], squares[b][r][c])
                 for r in range(n) for c in range(n)}
        if len(pairs) != n * n:
            raise ValueError(f"squares {a},{b}: not orthogonal")
    return n


def from_mols(squares):
    """Construct the full projective incidence object from a complete MOLS set.

    Point r*n+c is affine.  Point n*n+d is the point at infinity of
    direction d: row direction 0, column direction 1, square t direction t+2.
    The last line is the line at infinity.
    """
    n = check_complete_mols(squares)
    lines = []
    for r in range(n):
        lines.append([r * n + c for c in range(n)] + [n * n])
    for c in range(n):
        lines.append([r * n + c for r in range(n)] + [n * n + 1])
    for t, square in enumerate(squares):
        for symbol in range(n):
            lines.append([r * n + c for r in range(n) for c in range(n)
                          if square[r][c] == symbol] + [n * n + t + 2])
    lines.append(list(range(n * n, n * n + n + 1)))
    witness = {"order": n, "point_count": n * n + n + 1, "lines": lines}
    validate(witness)
    return witness


def validate(witness, expected_order=None):
    """Check a finite projective-plane witness directly; raise on any failure."""
    if not isinstance(witness, dict):
        raise ValueError("expected an incidence-object dictionary")
    n = witness.get("order")
    if type(n) is not int or n < 2:
        raise ValueError("order must be an integer at least 2")
    if expected_order is not None and n != expected_order:
        raise ValueError("wrong order")
    v = n * n + n + 1
    if witness.get("point_count") != v:
        raise ValueError("wrong point count")
    lines = witness.get("lines")
    if not isinstance(lines, list) or len(lines) != v:
        raise ValueError("wrong line count")
    line_sets = []
    on_lines = [set() for _ in range(v)]
    pair_line = {}
    for i, line in enumerate(lines):
        if not isinstance(line, list) or len(line) != n + 1:
            raise ValueError(f"line {i}: wrong degree")
        if any(type(p) is not int or not 0 <= p < v for p in line):
            raise ValueError(f"line {i}: invalid point")
        points = set(line)
        if len(points) != n + 1:
            raise ValueError(f"line {i}: repeated point")
        line_sets.append(points)
        for p in points:
            on_lines[p].add(i)
        for pair in combinations(sorted(points), 2):
            if pair in pair_line:
                raise ValueError("two points share more than one line")
            pair_line[pair] = i
    if len(pair_line) != v * (v - 1) // 2:
        raise ValueError("some point pair has no common line")
    if any(len(lines_at_p) != n + 1 for lines_at_p in on_lines):
        raise ValueError("wrong point degree")
    for a, b in combinations(range(v), 2):
        if len(line_sets[a] & line_sets[b]) != 1:
            raise ValueError("a line pair does not intersect in exactly one point")
    # Explicitly exhibit a quadrangle; this also rules out degenerate incidence
    # objects without trusting the parameter-count argument for nondegeneracy.
    a, b = 0, 1
    ab = line_sets[pair_line[(a, b)]]
    c = next((p for p in range(v) if p not in ab), None)
    if c is None:
        raise ValueError("no noncollinear triple")
    ac = line_sets[pair_line[tuple(sorted((a, c)))]]
    bc = line_sets[pair_line[tuple(sorted((b, c)))]]
    d = next((p for p in range(v) if p not in ab | ac | bc), None)
    if d is None:
        raise ValueError("no quadrangle")
    return {"valid": True, "order": n, "points": v, "lines": v,
            "points_per_line": n + 1, "lines_per_point": n + 1,
            "checked_point_pairs": v * (v - 1) // 2,
            "checked_line_pairs": v * (v - 1) // 2,
            "quadrangle": [a, b, c, d]}


def self_test():
    reports = []
    for prime in (2, 3, 5):
        squares = [[[(a * r + c) % prime for c in range(prime)]
                    for r in range(prime)] for a in range(1, prime)]
        witness = from_mols(squares)
        report = validate(witness, expected_order=prime)
        bad = {**witness, "lines": [row[:] for row in witness["lines"]]}
        bad["lines"][0][0] = bad["lines"][0][1]
        try:
            validate(bad)
        except ValueError:
            report["corrupted_incidence_rejected"] = True
        else:
            raise AssertionError("corrupted incidence was accepted")
        corrupted = [[row[:] for row in square] for square in squares]
        corrupted[0][0][0] = corrupted[0][0][1]
        try:
            from_mols(corrupted)
        except ValueError:
            report["corrupted_mols_rejected"] = True
        else:
            raise AssertionError("corrupted MOLS was accepted")
        reports.append(report)
    return reports


if __name__ == "__main__":
    import json
    print(json.dumps(self_test(), indent=2))
