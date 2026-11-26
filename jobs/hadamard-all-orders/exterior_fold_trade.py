"""Replay a nonzero physical fold change preserving the indexed modulo-eight projections."""

from collections import Counter
import json
from pathlib import Path

from exterior_mod16_invariant import decode, low_high_moments
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


def check_trade(certificate, previous, reference, source, exact):
    require(certificate["reference"] == 8 and certificate["new_columns"] == [2, 3],
            "reference factor number and zero-indexed fold coordinates")
    top, lower, upper_margin_rows, lower_margin_rows = source
    rows, before_rows = ([int(symbol, 32) for symbol in record["lower"]]
                         for record in (certificate, reference))
    upper = decode(previous["upper"])
    new, before = decode(certificate["lower"]), decode(reference["lower"])
    half = BOTTOM // 2
    require(len(rows) == len(before_rows) == BOTTOM, "physical lower row count")
    require((rows[0], rows[half]) == (before_rows[0], before_rows[half]), "border row pair")
    require([row.bit_count() for row in rows] == [row.bit_count() for row in lower_margin_rows]
            and [int(c, 32).bit_count() for c in previous["upper"]] == [m.bit_count() for m in upper_margin_rows],
            "all physical row margins")
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
    joint = tuple(sum((histogram(upper_dots, modulus) & histogram(negative_lower, modulus)).values())
                  for modulus in (8, 16, 32, 64, 4096))

    beta = [dots[index] for index in LOWER_OMISSIONS]
    before_beta = [before_dots[index] for index in LOWER_OMISSIONS]
    require(before_beta[1:] == [[-2 * value for value in row] for row in reference["factor"]],
            "reference omitted projection realizes factor eight")
    drift = tuple(tuple(b - a for a, b in zip(old, current, strict=True))
                  for old, current in zip(before_beta, beta, strict=True))
    alpha = correlations(top[1:3], upper, TOP)
    require(all(value == 0 for row in omitted_residual(alpha, before_beta, upper_gram) for value in row),
            "reference omitted Gram is exact")
    residual = omitted_residual(alpha, beta, upper_gram)
    changes = sum(a != b for a, b in zip(rows, before_rows, strict=True))
    if exact:
        require(beta == before_beta, "all 35 exact omitted dots preserved")
        require(all(value == 0 for row in residual for value in row), "all 25 exact omitted Gram entries")
        require(low_high_moments(upper_dots) == low_high_moments(negative_lower), "all mixed-bit moments")
        exact_matches = sum((Counter(map(tuple, upper_dots)) & Counter(map(tuple, negative_lower))).values())
        require(exact_matches == joint[-1], "modulo-4096 matches are exact integer matches")
        scalars = tuple(sum((Counter(row[j] % 16 for row in upper_dots)
                             & Counter(row[j] % 16 for row in negative_lower)).values()) for j in range(WIDTH))
        special = sum(tuple(value % 16 for value in row) == (6, 4, 12, 14, 14) for row in negative_lower)
        require((support.bit_count(), changes, joint, scalars, special)
                == (136, 233, (1193, 915, 278, 17, 10), (1189, 1171, 1177, 1169, 1161), 3),
                "recorded exact trade metrics")
        print(f"n=2396 exact indexed mod8 fold trade: {support.bit_count()} fold changes, "
              f"{changes} physical row changes, joint matches {joint}, scalar mod16 {scalars}, special count {special}; "
              "all exact omitted dots and both Gram conditions")
    else:
        require(drift == OMITTED_DRIFT, "recorded drift in the seven omitted projections")
        require(residual == OMITTED_GRAM_RESIDUAL, "recorded omitted Gram residual")
        omitted_l1 = sum(abs(value) for row in drift for value in row)
        joint8, joint16 = joint[:2]
        require((support.bit_count(), changes, joint8, joint16, omitted_l1) == (116, 214, 1193, 893, 400),
                "recorded trade metrics")
        print(f"n=2396 indexed mod8 fold trade: {support.bit_count()} fold changes, {changes} physical row changes, "
              f"{joint8} modulo-eight pairs, {joint16} modulo-sixteen pairs, omitted-dot drift L1 {omitted_l1}")


def main():
    directory = Path(__file__).parent
    previous = json.loads((directory / "exterior_mod16_invariant_witness.json").read_text())
    factors = json.loads((directory / "exterior_exact_factor_witnesses.json").read_text())
    source = gram_fixture()
    for name, exact in (("exterior_fold_trade_witness.json", False), ("exterior_fold_trade_exact_witness.json", True)):
        certificate = json.loads((directory / name).read_text())
        check_trade(certificate, previous, factors[7], source, exact)


if __name__ == "__main__":
    main()
