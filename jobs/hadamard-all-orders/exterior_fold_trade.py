"""Replay a nonzero physical fold change preserving the indexed modulo-eight projections."""

from collections import Counter
import json
from pathlib import Path

from exterior_mod16_invariant import decode
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture
from verify import paley


OMITTED_DRIFT = (
    (0, 0, 0, 0, 0),
    (16, 0, 64, -80, 0),
    (-24, 0, 0, 0, 24),
    (0, 0, -48, 80, -32),
    (0, 0, -8, 0, 8),
    (0, 0, 0, 0, 0),
    (8, 0, -8, 0, 0),
)
OMITTED_GRAM_RESIDUAL = (
    (-18816, 4992, -16096, 24992, 4928),
    (4992, 0, 9152, -16640, 2496),
    (-16096, 9152, -26560, 23296, 10208),
    (24992, -16640, 23296, -26880, -4768),
    (4928, 2496, 10208, -4768, -12864),
)


def histogram(dots, modulus):
    return Counter(tuple(value % modulus for value in row) for row in dots)


def omitted_residual(alpha, beta, upper_gram):
    return tuple(tuple(sum(row[i] * row[j] for row in beta[1:])
                       - sum(row[i] * row[j] for row in alpha)
                       - ORDER * (BOTTOM * (i == j) - upper_gram[i][j])
                       for j in range(WIDTH)) for i in range(WIDTH))


def main():
    directory = Path(__file__).parent
    certificate = json.loads((directory / "exterior_fold_trade_witness.json").read_text())
    previous = json.loads((directory / "exterior_mod16_invariant_witness.json").read_text())
    factors = json.loads((directory / "exterior_exact_factor_witnesses.json").read_text())
    require(certificate["reference"] == 8 and certificate["new_columns"] == [2, 3],
            "reference factor number and zero-indexed fold coordinates")
    reference = factors[certificate["reference"] - 1]
    top, lower, _, lower_margin_rows = gram_fixture()
    rows, before_rows = ([int(symbol, 32) for symbol in record["lower"]]
                         for record in (certificate, reference))
    upper = decode(previous["upper"])
    new, before = decode(certificate["lower"]), decode(reference["lower"])
    half = BOTTOM // 2
    require(len(rows) == len(before_rows) == BOTTOM, "physical lower row count")
    require((rows[0], rows[half]) == (before_rows[0], before_rows[half]), "border row pair")
    require([row.bit_count() for row in rows] == [row.bit_count() for row in lower_margin_rows], "row margins")
    require(all(a.bit_count() == b.bit_count() and (a >> half).bit_count() == (b >> half).bit_count()
                for a, b in zip(before, new, strict=True)), "both exact half column weights")
    require(all(a.bit_count() + b.bit_count() == ORDER // 2
                for a, b in zip(upper, new, strict=True)), "exact outer column balance")
    upper_gram = correlations(upper, upper, TOP)
    new_gram = correlations(new, new, BOTTOM)
    require(all(upper_gram[i][j] + new_gram[i][j] == ORDER * (i == j)
                for i in range(WIDTH) for j in range(WIDTH)), "exact outer new Gram")

    toggle = sum(1 << j for j in certificate["new_columns"])
    fold_differences = [rows[r] ^ rows[r + half] ^ before_rows[r] ^ before_rows[r + half] for r in range(half)]
    require(set(fold_differences) == {0, toggle}, "only the two recorded fold coordinates change")
    support = sum(1 << r for r, change in enumerate(fold_differences) if change)
    require(all((support & column).bit_count() % 2 == 0 for column in paley(half - 1)),
            "fold support is orthogonal to every positive Paley column")
    before_dots = correlations(lower, before, BOTTOM)
    dots = correlations(lower, new, BOTTOM)
    require(all((x - y) % 8 == 0 for a, b in zip(before_dots, dots, strict=True)
                for x, y in zip(a, b, strict=True)), "all indexed lower projections remain the same modulo eight")
    upper_dots = correlations(top[3:], upper, TOP)
    negative_lower = [[-value for value in row] for i, row in enumerate(dots) if i not in LOWER_OMISSIONS]
    joint8, joint16 = (sum((histogram(upper_dots, modulus) & histogram(negative_lower, modulus)).values())
                       for modulus in (8, 16))

    beta = [dots[index] for index in LOWER_OMISSIONS]
    before_beta = [before_dots[index] for index in LOWER_OMISSIONS]
    require(before_beta[1:] == [[-2 * value for value in row] for row in reference["factor"]],
            "reference omitted projection realizes factor eight")
    drift = tuple(tuple(b - a for a, b in zip(old, current, strict=True))
                  for old, current in zip(before_beta, beta, strict=True))
    require(drift == OMITTED_DRIFT, "recorded drift in the seven omitted projections")
    alpha = correlations(top[1:3], upper, TOP)
    require(all(value == 0 for row in omitted_residual(alpha, before_beta, upper_gram) for value in row),
            "reference omitted Gram is exact")
    require(omitted_residual(alpha, beta, upper_gram) == OMITTED_GRAM_RESIDUAL, "recorded omitted Gram residual")
    changes = sum(a != b for a, b in zip(rows, before_rows, strict=True))
    omitted_l1 = sum(abs(value) for row in drift for value in row)
    require((support.bit_count(), changes, joint8, joint16, omitted_l1) == (116, 214, 1193, 893, 400),
            "recorded trade metrics")
    print(f"n=2396 indexed mod8 fold trade: {support.bit_count()} fold changes, {changes} physical row changes, "
          f"{joint8} modulo-eight pairs, {joint16} modulo-sixteen pairs, omitted-dot drift L1 {omitted_l1}")


if __name__ == "__main__":
    main()
