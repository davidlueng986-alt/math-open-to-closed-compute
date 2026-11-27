"""Independently replay the fixed H(44), pivot-zero signature atlas."""

from hashlib import sha256
from itertools import combinations
import json
import lzma
from math import comb
from pathlib import Path


HERE = Path(__file__).resolve().parent
FIELD = 43
WIDTH = 21
WEIGHT = 10
MODULUS = 101
HEX_DIGITS = b"0123456789abcdef"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def positive(row, column):
    """Paley sign at two finite labels, using Euler's criterion."""
    return pow((column - row) % FIELD, (FIELD - 1) // 2, FIELD) == 1


def group_masks(rows, points, complemented=False):
    return tuple(
        sum(1 << index for index, row in enumerate(rows) if positive(row, point) != complemented)
        for point in points
    )


def matrix_data():
    finite = range(1, FIELD)
    residues = tuple(point for point in finite if positive(0, point))
    nonresidues = tuple(point for point in finite if not positive(0, point))
    require(len(residues) == len(nonresidues) == WIDTH, "Paley halves have the wrong size")
    left = group_masks(nonresidues, nonresidues)
    right = group_masks(residues, nonresidues, complemented=True)
    for half in (left, right):
        require(all(mask.bit_count() == WEIGHT for mask in half), "wrong point degrees")
        require(all(sum(mask >> r & 1 for mask in half) == WEIGHT for r in range(WIDTH)),
                "wrong block degrees")
    for i, j in combinations(range(WIDTH), 2):
        total = (left[i] & left[j]).bit_count() + (right[i] & right[j]).bit_count()
        require(total == WEIGHT - 1, "wrong combined Gram off-diagonal")
    inside_masks = zip(group_masks(nonresidues, residues), group_masks(residues, residues), strict=True)
    known = {pair: point + 1 for pair, point in zip(inside_masks, residues, strict=True)}
    require(len(known) == WIDTH, "known H44 inside columns must be distinct")
    return left, right, known, nonresidues, residues


def selectors():
    return combinations(range(WIDTH), WEIGHT)


def bit_mask(indices):
    return sum(1 << i for i in indices)


def signature(point_masks, selector):
    return bytes(HEX_DIGITS[(point_mask & selector).bit_count()] for point_mask in point_masks)


def determinant_and_solution(left, right):
    """Row reduce an invertible square system over the prime field F_101."""
    matrix = [list(row) + list(rhs) for row, rhs in zip(left, right, strict=True)]
    determinant = 1
    for i in range(len(matrix)):
        pivot = next((r for r in range(i, len(matrix)) if matrix[r][i]), None)
        require(pivot is not None, "signature system is singular over F_101")
        if pivot != i:
            matrix[i], matrix[pivot] = matrix[pivot], matrix[i]
            determinant = -determinant
        pivot_value = matrix[i][i]
        determinant = determinant * pivot_value % MODULUS
        inverse = pow(pivot_value, -1, MODULUS)
        matrix[i] = [x * inverse % MODULUS for x in matrix[i]]
        for r, row in enumerate(matrix):
            if r != i and row[i]:
                scale = row[i]
                matrix[r] = [(x - scale * y) % MODULUS for x, y in zip(row, matrix[i], strict=True)]
    return determinant, [row[len(matrix):] for row in matrix]


def collisions(left, right):
    """Solve Bᵀv=Aᵀu independently of the packed-sum histogram search."""
    a_t = [tuple(mask >> i & 1 for i in range(WIDTH)) for mask in left]
    b_t = [tuple(mask >> i & 1 for i in range(WIDTH)) for mask in right]
    det_a, _ = determinant_and_solution(a_t, [()] * WIDTH)
    det_b, transform = determinant_and_solution(b_t, a_t)
    require((det_a, det_b) == (53, 73), "unexpected determinants modulo 101")

    # Each true pair has a unique candidate v because Bᵀ is invertible.
    # Binary vectors have unique representatives, and each signature digit is below 101.
    matches = {}
    for selected in selectors():
        right_mask = 0
        for i, equation in enumerate(transform):
            value = sum(equation[j] for j in selected) % MODULUS
            if value > 1:
                break
            right_mask |= value << i
        else:
            if right_mask.bit_count() != WEIGHT:
                continue
            left_mask = bit_mask(selected)
            key = signature(left, left_mask)
            require(signature(right, right_mask) == key, "modular candidate fails exact equations")
            require(key not in matches, "invertible signature map duplicated a key")
            matches[key] = (left_mask, right_mask)
    return matches


def verify_histogram(path, point_masks):
    """Check every archive entry against direct column-mask intersections."""
    keys = sorted(signature(point_masks, bit_mask(choice)) for choice in selectors())
    require(len(keys) == comb(WIDTH, WEIGHT), "wrong subset total")
    digest = sha256()
    with lzma.open(path, "rb") as stream:
        for key, line in zip(keys, stream, strict=True):
            require(line == key + b"\t1\n", f"wrong canonical entry in {path.name}")
            digest.update(line)
    return digest.hexdigest()


def example(pair, known, positive_rows, negative_rows):
    u, v = pair
    a_rows = [i for i in range(WIDTH) if u >> i & 1]
    b_rows = [i for i in range(WIDTH) if v >> i & 1]
    selected = [positive_rows[i] for i in a_rows] + [negative_rows[i] for i in b_rows]
    return {
        "a_rows": a_rows,
        "b_rows": b_rows,
        "selected_original_zero_based_rows": sorted(selected),
        "original_inner_column": known[pair],
    }


def verify_summary(matches, known, nonresidues, residues, hashes):
    summary = json.loads((HERE / "atlas.json").read_text(encoding="utf-8"))
    require(summary["order20_control"] == {"N1": 9, "N2": 36}, "wrong order-20 control")
    atlas = summary["order44"]
    positive_rows = [r + 1 for r in nonresidues]
    negative_rows = [r + 1 for r in residues]
    pair_count = sum((u & u_next).bit_count() + (v & v_next).bit_count() == WEIGHT - 1
                     for (u, v), (u_next, v_next) in combinations(matches.values(), 2))
    require(pair_count == comb(WIDTH, 2), "the H44 collisions must form a full clique")
    expected = {
        "order": FIELD + 1,
        "pivot_index_in_outside": 0,
        "original_pivot_column": 1,
        "original_finite_point_columns": positive_rows,
        "positive_original_rows": positive_rows,
        "negative_original_rows": negative_rows,
        "shared_signatures": len(matches),
        "N1": len(matches),
        "N2": pair_count,
        "known_clique_size": len(known),
        "extra_vertices": len(set(matches.values()) - known.keys()),
    }
    for field, value in expected.items():
        require(atlas[field] == value, f"incorrect atlas metadata field {field}")
    count = comb(WIDTH, WEIGHT)
    for side, digest in hashes.items():
        require(atlas["sides"][side] == {
            "subsets": count,
            "distinct": count,
            "multiplicity_counts": {"1": count},
            "uncompressed_bytes": count * (WIDTH + 3),
            "sha256": digest,
            "filename": f"h44-{side}.tsv.xz",
        }, f"incorrect archive metadata for {side}")
    ordered = sorted(matches.items())
    require(atlas["matches"] == [
        {"signature": key.decode(), "a_multiplicity": 1, "b_multiplicity": 1, "a_masks": [u], "b_masks": [v]}
        for key, (u, v) in ordered
    ], "atlas collision inventory disagrees with independent solve")
    require(atlas["decoded_examples"] == [
        example(pair, known, positive_rows, negative_rows) for _, pair in ordered[:2]
    ], "incorrect decoding of example subsets")


def main():
    left, right, known, nonresidues, residues = matrix_data()
    matches = collisions(left, right)
    require(set(matches.values()) == known.keys(), "the atlas contains a different class of collisions")
    hashes = {side: verify_histogram(HERE / f"h44-{side}.tsv.xz", masks)
              for side, masks in (("a", left), ("b", right))}
    verify_summary(matches, known, nonresidues, residues, hashes)
    print(f"H44 pivot zero: both archives match all {comb(WIDTH, WEIGHT):,} direct signatures.")
    print(f"Exact modular replay finds {len(matches)} collisions, precisely the known H44 inside columns.")
    for side, digest in hashes.items():
        print(f"{side.upper()} canonical SHA256 {digest}")


if __name__ == "__main__":
    main()
