"""Replay three exact five-column profiles beyond fixed folded-pool counts."""

from collections import Counter
import json
from pathlib import Path

from exterior_mod16_invariant import decode, low_high_moments
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture, match_by_residues


MODULI = (8, 16, 32, 64, 4096)
SPECIAL_VECTOR = (6, 4, 12, 14, 14)
EXPECTED = {
    "joint": ((1193, 999, 271, 31, 9), (1183, 1185, 1173, 1191, 1177), 5, 218),
    "special": ((1193, 996, 266, 29, 12), (1185, 1175, 1167, 1143, 1185), 3, 214),
    "scalar": ((1193, 940, 283, 24, 10), (1193, 1193, 1193, 1193, 1193), 9, 204),
}


def histogram(dots, modulus):
    return Counter(tuple(value % modulus for value in row) for row in dots)


def folded_pools(rows):
    half = BOTTOM // 2
    return Counter((a ^ b, a.bit_count(), b.bit_count(), a)
                   for a, b in zip(rows[:half], rows[half:], strict=True))


def main():
    directory = Path(__file__).parent
    previous = json.loads((directory / "exterior_mod16_invariant_witness.json").read_text())
    profiles = json.loads((directory / "exterior_wide_fold_witnesses.json").read_text())
    require(set(profiles) == set(EXPECTED), "all specified witness profiles")
    top, lower, _, _ = gram_fixture()
    upper = decode(previous["upper"])
    original = decode(previous["lower"])
    old_rows = [int(symbol, 32) for symbol in previous["lower"]]
    half = BOTTOM // 2
    fold = [a ^ b for a, b in zip(old_rows[:half], old_rows[half:], strict=True)]
    omitted = [lower[i] for i in LOWER_OMISSIONS]
    retained = [column for i, column in enumerate(lower) if i not in LOWER_OMISSIONS]
    old_dots = correlations(retained, original, BOTTOM)
    upper_dots = correlations(top[3:], upper, TOP)
    alpha = correlations(top[1:3], upper, TOP)
    beta = correlations(omitted[1:], original, BOTTOM)
    gram = correlations(upper, upper, TOP)
    upper_special = sum(tuple(value % 16 for value in row) == SPECIAL_VECTOR for row in upper_dots)
    require(upper_special == 3, "upper special residue multiplicity")

    for name, expected in EXPECTED.items():
        rows = [int(symbol, 32) for symbol in profiles[name]]
        require(len(rows) == BOTTOM and (rows[0], rows[half]) == (old_rows[0], old_rows[half]),
                "physical row count and fixed border pair")
        require([r.bit_count() for r in rows] == [r.bit_count() for r in old_rows], "exact row margins")
        require([a ^ b for a, b in zip(rows[:half], rows[half:], strict=True)] == fold,
                "physical folded XOR preserved")
        require(folded_pools(rows) != folded_pools(old_rows), "pool counts genuinely changed")
        new = decode(profiles[name])
        require(all(a.bit_count() == b.bit_count() and (a >> half).bit_count() == (b >> half).bit_count()
                    for a, b in zip(original, new, strict=True)), "both half column weights preserved")
        require(all(a.bit_count() + b.bit_count() == ORDER // 2
                    for a, b in zip(upper, new, strict=True)), "exact column balance")
        require(correlations(omitted, new, BOTTOM) == correlations(omitted, original, BOTTOM),
                "all exact omitted projections preserved")
        new_gram = correlations(new, new, BOTTOM)
        for i in range(WIDTH):
            for j in range(WIDTH):
                require(gram[i][j] + new_gram[i][j] == ORDER * (i == j),
                        "all new/new orthogonalities")
                require(sum(row[i] * row[j] for row in beta) - sum(row[i] * row[j] for row in alpha)
                        == ORDER * (BOTTOM * (i == j) - gram[i][j]), "exact omitted Gram")

        lower_dots = correlations(retained, new, BOTTOM)
        require(all((x - y) % 8 == 0
                    for a, b in zip(old_dots, lower_dots, strict=True)
                    for x, y in zip(a, b, strict=True)), "each indexed residue preserved modulo eight")
        negative_lower = [[-value for value in row] for row in lower_dots]
        require(low_high_moments(upper_dots) == low_high_moments(negative_lower), "mixed-bit condition")
        joint = tuple(sum((histogram(upper_dots, m) & histogram(negative_lower, m)).values())
                      for m in MODULI)
        scalar = tuple(sum((Counter(row[j] % 16 for row in upper_dots)
                            & Counter(row[j] % 16 for row in negative_lower)).values())
                       for j in range(WIDTH))
        special = sum(tuple(value % 16 for value in row) == SPECIAL_VECTOR for row in negative_lower)
        changed = sum(a != b for a, b in zip(rows, old_rows, strict=True))
        require((joint, scalar, special, changed) == expected, "joint and scalar multiplicities and row changes")
        pairing = match_by_residues(upper_dots, negative_lower,
                                    levels=tuple(zip(reversed(MODULI), reversed(joint), strict=True)))
        exact = sum(a == b for i, j in pairing
                    for a, b in zip(upper_dots[i], negative_lower[j], strict=True))
        print(f"n=2396 {name}: joint vectors {joint}; scalar mod16 {scalar}; special count {special}; "
              f"{changed} changed rows; {exact}/5965 exact scalar dots in the hierarchical pairing")


if __name__ == "__main__":
    main()
