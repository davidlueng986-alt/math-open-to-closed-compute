"""Check the absolute Sylvester–Paley mixed-bit invariant and two upper profiles."""

import json
from collections import Counter
from itertools import combinations_with_replacement
from pathlib import Path

from exterior_lower_fiber import binary_echelon
from five_column_constraints import (
    BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, positive_columns,
    require, rows_from_columns,
)
from five_column_gram import gram_fixture, match_by_residues


def low_high_moments(dots):
    """Unordered 5-by-5 parity of products of the bits for 4 and 8."""
    return [
        sum((row[i] >> 2 & 1) * (row[j] >> 3 & 1) for row in dots) % 2
        for i in range(WIDTH) for j in range(WIDTH)
    ]


def possible_copy_offsets(retained, constant, omitted_masks):
    """Necessary XOR shifts between the lower Sylvester copies."""
    counts = Counter(sum((value >> 2 & 1) << i for i, value in enumerate(row))
                     for row in retained + [constant])
    counts.update(omitted_masks)
    offsets = [0] if all(count % 2 == 0 for count in counts.values()) else []
    offsets.extend(mask for mask in range(1, 1 << WIDTH)
                   if mask.bit_count() % 2 == 0
                   and all(counts[value] == counts[value ^ mask] for value in range(1 << WIDTH)))
    return offsets


def omitted_residue_census(top, upper):
    """Count unordered low-mask profiles that can satisfy each necessary condition."""
    retained = correlations(top[3:], upper, TOP)
    low_constants = [value % 4 // 2 for value in retained[0]]
    require(all(value % 4 == 2 * residue
                for row in retained for value, residue in zip(row, low_constants, strict=True)),
            "each upper coordinate has a common even residue modulo four")
    constant_omission = [TOP - 2 * column.bit_count() for column in upper]
    require(all(value % 4 == 2 * residue
                for value, residue in zip(constant_omission, low_constants, strict=True)),
            "known signed constant omission has the same low residue")
    moment_target = [
        a ^ b for a, b in zip(low_high_moments(retained),
                              low_high_moments([constant_omission]), strict=True)
    ]
    gram = correlations(upper, upper, TOP)
    alpha = correlations(top[1:3], upper, TOP)
    pairs = [(i, j) for i in range(WIDTH) for j in range(i + 1)]
    gram_target = [
        (ORDER // 4) * (BOTTOM * (i == j) - gram[i][j])
        + sum((row[i] // 2) * (row[j] // 2) for row in alpha)
        for i, j in pairs
    ]

    rows = len(LOWER_OMISSIONS) - 1
    row_sum = -(ORDER // 4)
    base_sum = sum(low_constants)
    masks = [mask for mask in range(1 << WIDTH)
             if (row_sum - base_sum - 2 * mask.bit_count()) % 4 == 0]
    require(len(masks) == 16, "sixteen allowed low masks per omitted row")
    bases = [[constant + 2 * (mask >> j & 1)
              for j, constant in enumerate(low_constants)] for mask in masks]
    products = [[base[i] * base[j] for i, j in pairs] for base in bases]
    row_masks = [((1 << WIDTH) - 1) << (WIDTH * r) for r in range(rows)]
    columns = [sum(1 << (WIDTH * r + j) for r in range(rows)) for j in range(WIDTH)]
    gram_masks = [
        (columns[j] if low_constants[i] else 0) ^ (columns[i] if low_constants[j] else 0)
        for i, j in pairs
    ]

    low_count = high_count = 0
    compatible = []
    for profile in combinations_with_replacement(range(len(masks)), rows):
        differences = [target - sum(products[k][p] for k in profile)
                       for p, target in enumerate(gram_target)]
        if any(value % 4 for value in differences):
            continue
        low_count += 1
        selected = tuple(masks[k] for k in profile)
        equations = [(mask, value // 4 % 2)
                     for mask, value in zip(gram_masks, differences, strict=True)]
        equations.extend((row, (row_sum - base_sum - 2 * mask.bit_count()) // 4 % 2)
                         for row, mask in zip(row_masks, selected, strict=True))
        if binary_echelon(equations) is None:
            continue
        high_count += 1
        for i in range(WIDTH):
            support = sum(row for row, mask in zip(row_masks, selected, strict=True) if mask >> i & 1)
            equations.extend((support & columns[j], moment_target[WIDTH * i + j]) for j in range(WIDTH))
        pivots = binary_echelon(equations)
        if pivots is not None:
            compatible.append((selected, len(pivots)))
    return low_count, high_count, compatible


def decode(encoded):
    return positive_columns([int(symbol, 32) for symbol in encoded])


def main():
    top, lower, reference_top_rows, reference_lower_rows = gram_fixture()
    old_witnesses = json.loads(Path(__file__).with_name("exterior_lift_witnesses.json").read_text())
    new_witness = json.loads(Path(__file__).with_name("exterior_mod16_invariant_witness.json").read_text())
    blocked_top = decode(old_witnesses["hybrid_upper"])
    blocked_lower = decode(old_witnesses["hybrid_lower"])
    eligible_top = decode(new_witness["upper"])
    eligible_lower = decode(new_witness["lower"])

    for source, length, new, reference_rows, omissions in (
        (top, TOP, eligible_top, reference_top_rows, (0, 1, 2)),
        (lower, BOTTOM, eligible_lower, reference_lower_rows, LOWER_OMISSIONS),
    ):
        original = positive_columns(reference_rows)
        actual_rows = rows_from_columns(length, new)
        original_rows = rows_from_columns(length, original)
        require(actual_rows[0] == original_rows[0], "fixed border signs")
        require([row.bit_count() for row in actual_rows] == [row.bit_count() for row in original_rows],
                "exact physical row margins")
        omitted = [source[i] for i in omissions]
        require(correlations(omitted, new, length) == correlations(omitted, original, length),
                "each exact omitted projection, including column weights")

    require(all(a.bit_count() + b.bit_count() == ORDER // 2
                for a, b in zip(eligible_top, eligible_lower, strict=True)), "exact column balance")
    gram_top = correlations(eligible_top, eligible_top, TOP)
    gram_lower = correlations(eligible_lower, eligible_lower, BOTTOM)
    alpha = correlations(top[1:3], eligible_top, TOP)
    beta = correlations([lower[i] for i in LOWER_OMISSIONS[1:]], eligible_lower, BOTTOM)
    for i in range(WIDTH):
        for j in range(WIDTH):
            require(gram_top[i][j] + gram_lower[i][j] == ORDER * (i == j), "exact new/new Gram")
            require(sum(row[i] * row[j] for row in beta) - sum(row[i] * row[j] for row in alpha)
                    == ORDER * (BOTTOM * (i == j) - gram_top[i][j]), "exact omitted Gram entry")

    for label, new_top, new_lower, expected in (
        ("994", blocked_top, blocked_lower, (3384, 143, [])),
        ("988", eligible_top, eligible_lower, (3384, 143, [((2, 4, 7, 25, 26, 28), 22)])),
    ):
        upper_dots = correlations(top[3:], new_top, TOP)
        lower_dots = [[-value for value in row] for row in correlations(lower, new_lower, BOTTOM)]
        retained = [row for i, row in enumerate(lower_dots) if i not in LOWER_OMISSIONS]
        require(low_high_moments(lower_dots) == [0] * (WIDTH * WIDTH), "absolute lower moments")
        mismatches = sum(a != b for a, b in zip(low_high_moments(upper_dots),
                                               low_high_moments(retained), strict=True))
        require(mismatches == (14 if label == "994" else 0), "mixed-bit parity defect count")
        actual = omitted_residue_census(top, new_top)
        require(actual == expected, "complete omitted residue census")
        print(f"n=2396 {label} upper: {actual[0]} low Gram profiles, {actual[1]} Gram lifts, "
              f"{len(actual[2])} pass the mixed-bit condition")
        if label == "988":
            offset = possible_copy_offsets(upper_dots, lower_dots[0], actual[2][0][0])
            require(offset == [20], "unique necessary Sylvester copy offset")
            actual_offset = sum(((column >> (BOTTOM // 2)).bit_count() % 2) << j
                                for j, column in enumerate(new_lower))
            require(actual_offset == offset[0], "the recorded lower copy offset")
            levels = ((4096, 9), (64, 28), (32, 281), (16, 988), (8, 1193))
            pairing = match_by_residues(upper_dots, retained, levels=levels)
            scalar_zeros = sum(a == b for i, j in pairing
                               for a, b in zip(upper_dots[i], retained[j], strict=True))
            require(scalar_zeros == 1145, "exact scalar mixed zeros in the recorded pairing")
            print("  eligible witness: exact margins and Grams; 1193 vectors modulo 8, "
                  "988 modulo 16, 281 modulo 32, 28 modulo 64, 9 exact")
            print("  required lower Sylvester copy offset: mask 20")
            print(f"  {scalar_zeros}/5965 individual mixed products are exactly zero")


if __name__ == "__main__":
    main()
