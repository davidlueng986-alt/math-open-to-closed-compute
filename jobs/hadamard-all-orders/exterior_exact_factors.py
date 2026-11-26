"""Derive and verify the exhaustive exact omitted-factor census for the 988 upper."""

import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess

from exterior_mod16_invariant import decode, low_high_moments, omitted_residue_census
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture


def low_mask(row):
    return sum((value >> 1 & 1) << j for j, value in enumerate(row))


def derive_problem():
    top, lower, _, _ = gram_fixture()
    data = json.loads(Path(__file__).with_name("exterior_mod16_invariant_witness.json").read_text())
    upper, bottom = decode(data["upper"]), decode(data["lower"])
    _, _, profiles = omitted_residue_census(top, upper)
    require(len(profiles) == 1, "one possible unordered omitted low profile")
    selected, _ = profiles[0]
    require(len(selected) == len(set(selected)), "distinct masks specify a canonical row order")

    dots = correlations(top[3:], upper, TOP)
    residues = [value % 4 // 2 for value in dots[0]]
    constant = [TOP - 2 * column.bit_count() for column in upper]
    target = [a ^ b for a, b in zip(low_high_moments(dots), low_high_moments([constant]), strict=True)]
    alpha = correlations(top[1:3], upper, TOP)
    top_gram = correlations(upper, upper, TOP)
    gram = [[sum((row[i] // 2) * (row[j] // 2) for row in alpha)
             + (ORDER // 4) * (BOTTOM * (i == j) - top_gram[i][j])
             for j in range(WIDTH)] for i in range(WIDTH)]
    row_sum = -(ORDER // 4)
    require(all(sum(row) % row_sum == 0 for row in gram), "integral factor column sums")
    column_sums = [sum(row) // row_sum for row in gram]

    # The mixed-bit equations act independently on the high bits of each
    # column once the low row masks have been fixed.
    rows = len(selected)
    low_residues = [[a + 2 * (mask >> j & 1) for mask in selected]
                    for j, a in enumerate(residues)]
    supports = [sum((mask >> i & 1) << r for r, mask in enumerate(selected)) for i in range(WIDTH)]
    high_masks = [[candidate for candidate in range(1 << rows)
                   if all((support & candidate).bit_count() % 2 == target[i * WIDTH + j]
                          for i, support in enumerate(supports))]
                  for j in range(WIDTH)]
    require([len(options) for options in high_masks] == [4] * WIDTH, "four high masks per column")
    recorded_projections = correlations([lower[i] for i in LOWER_OMISSIONS[1:]], bottom, BOTTOM)
    recorded = tuple(sorted((tuple(-value // 2 for value in row) for row in recorded_projections),
                            key=low_mask))
    return gram, row_sum, column_sums, low_residues, high_masks, recorded


def check_lower_realizations(factors):
    top, lower, _, reference_lower = gram_fixture()
    witness_path = Path(__file__).with_name("exterior_mod16_invariant_witness.json")
    upper = decode(json.loads(witness_path.read_text())["upper"])
    upper_gram = correlations(upper, upper, TOP)
    upper_dots = correlations(top[3:], upper, TOP)
    omissions = [lower[i] for i in LOWER_OMISSIONS]
    retained_lower = [column for i, column in enumerate(lower) if i not in LOWER_OMISSIONS]
    weights = [mask.bit_count() for mask in reference_lower]

    def histogram(dots, modulus):
        return Counter(tuple(value % modulus for value in row) for row in dots)

    upper_mod8 = histogram(upper_dots, 8)
    upper_mod16 = histogram(upper_dots, 16)
    table_path = Path(__file__).with_name("exterior_exact_factor_witnesses.json")
    seen = set()
    mod16_counts = []
    for witness in json.loads(table_path.read_text()):
        factor = tuple(tuple(row) for row in witness["factor"])
        require(factor in factors and factor not in seen, "one lower witness per factor")
        require(len(witness["lower"]) == BOTTOM
                and [int(symbol, 32).bit_count() for symbol in witness["lower"]] == weights,
                "all lower physical row margins and the border signs")
        columns = decode(witness["lower"])
        require(all(a.bit_count() + b.bit_count() == ORDER // 2
                    for a, b in zip(upper, columns, strict=True)), "exact whole-column balance")
        lower_gram = correlations(columns, columns, BOTTOM)
        require(all(upper_gram[i][j] + lower_gram[i][j] == ORDER * (i == j)
                    for i in range(WIDTH) for j in range(WIDTH)), "exact new/new orthogonality")
        require(correlations(omissions[1:], columns, BOTTOM) == [[-2 * value for value in row] for row in factor],
                "actual projected factor in canonical physical omission order")
        lower_dots = [[-value for value in row] for row in correlations(retained_lower, columns, BOTTOM)]
        require(histogram(lower_dots, 8) == upper_mod8, "all 1193 mixed vectors can pair modulo eight")
        mod16_counts.append(sum((upper_mod16 & histogram(lower_dots, 16)).values()))
        seen.add(factor)
    require(seen == factors, "all eight factors realized in the lower sign rows")
    require(mod16_counts == [882, 918, 935, 891, 911, 899, 912, 922], "eight modulo-sixteen matching counts")
    return mod16_counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", type=Path, help="compiled exterior_exact_factors enumerator")
    args = parser.parse_args()
    gram, row_sum, column_sums, low, high, recorded = derive_problem()
    bound = BOTTOM // 2
    entries = [[bound, row_sum], *gram, column_sums, *low, *[[len(options), *options] for options in high]]
    search = subprocess.run(
        [str(args.executable.resolve())],
        input="".join(" ".join(map(str, line)) + "\n" for line in entries),
        text=True, check=True, capture_output=True,
    )
    require(search.stderr.splitlines() == [
        "column choices 303768 128286 73560 281985 29190",
        "exact prefix counts 961636 21762 8 8",
    ], "exact census counts of eligible vectors and prefixes")

    factors = set()
    for line in search.stdout.splitlines():
        values = [int(value) for value in line.split()]
        require(len(values) == len(low[0]) * WIDTH, "factor shape")
        factor = tuple(tuple(values[i:i + WIDTH]) for i in range(0, len(values), WIDTH))
        columns = list(zip(*factor, strict=True))
        require(factor not in factors and all(sum(row) == row_sum for row in factor),
                "distinct canonical factors with prescribed row sums")
        require(all(abs(value) <= bound for row in factor for value in row), "bounded real projections")
        for j, col in enumerate(columns):
            require(sum(col) == column_sums[j], "prescribed column sums")
            require([value % 4 for value in col] == low[j], "prescribed low residues")
            high_mask = sum((value >> 2 & 1) << r for r, value in enumerate(col))
            require(high_mask in high[j], "necessary high-bit moments")
            require(all(sum(a * b for a, b in zip(col, other, strict=True)) == gram[j][k]
                        for k, other in enumerate(columns)), "all entries of the exact Gram")
        factors.add(factor)
    require(len(factors) == 8 and recorded in factors, "eight factors including the recorded projections")
    reflection = (1, -1, 0, 0, -1, 1)
    for factor in factors:
        values = [sum(u * row[j] for u, row in zip(reflection, factor, strict=True))
                  for j in range(WIDTH)]
        require(all(value % 2 == 0 for value in values), "integral reflected factor")
        reflected = tuple(tuple(value - u * projection // 2
                                for value, projection in zip(row, values, strict=True))
                          for u, row in zip(reflection, factor, strict=True))
        require(reflected in factors and reflected != factor, "four reflection pairs")
    mod16_counts = check_lower_realizations(factors)
    print(search.stderr, end="")
    for factor in sorted(factors):
        print(json.dumps(factor))
    print("n=2396: exactly eight necessary exact omitted projection factors in four reflection pairs")
    print("  all eight satisfy the exact margins and Grams and all 1193 vector matches modulo eight")
    print(f"  full vector matches modulo sixteen: {mod16_counts}")


if __name__ == "__main__":
    main()
