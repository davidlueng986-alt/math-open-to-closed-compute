"""Replay an exact matching upper bound and a stronger witness at the 136-support fold."""

from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
import json

from exterior_fold_trade import omitted_residual
from exterior_mod16_invariant import decode, low_high_moments
from five_column_constraints import BOTTOM, LOWER_OMISSIONS, ORDER, TOP, WIDTH, correlations, require
from five_column_gram import gram_fixture
from verify import paley, rows_from_columns


def residue(row):
    return tuple(value % 8 for value in row)


def pair_data(rows):
    half = BOTTOM // 2
    folds = [x ^ y for x, y in zip(rows[:half], rows[half:], strict=True)]
    options = [tuple(x for x in range(1 << WIDTH) if x.bit_count() == rows[r].bit_count()
                     and (x ^ fold).bit_count() == rows[r+half].bit_count())
               for r, fold in enumerate(folds)]
    return folds, options


def check_hall(certificate, rows, upper_dots, lower_dots, retained, separate_halves):
    half = BOTTOM // 2
    folds, options = pair_data(rows)
    columns = paley(half - 1)
    require(len(options[0]) == 1, "first sign row and its folded partner are fixed")
    require(any(index >= half for index in LOWER_OMISSIONS[1:]), "an exact omitted minus-copy projection")

    def dot_change(index, r, first_sign, copy):
        return -first_sign * (2 * (columns[index % half] >> r & 1) - 1) if index // half == copy else 0

    column_data = []
    for j in range(WIDTH):
        flexible = [r for r in range(1, half) if any((x ^ rows[r]) >> j & 1 for x in options[r])]
        signs = [(r, 1 - 2 * (rows[r] >> j & 1), folds[r] >> j & 1) for r in flexible]
        features = []
        for r, u, copy in signs:
            v = 1 - 2 * (rows[r+half] >> j & 1)
            weight = (u, v) if separate_halves else (u + v,)
            features.append(weight + tuple(dot_change(index, r, u, copy) for index in LOWER_OMISSIONS[1:]))
        column_data.append((signs, features))

    schedules = []
    for j, direction, raw_prices in certificate["prices"]:
        require(0 <= j < WIDTH and direction in (-1, 1) and len(raw_prices) == 7 + separate_halves,
                "scalar price shape")
        price = [Fraction(x, y) for x, y in raw_prices]
        signs, features = column_data[j]
        charged = [sum(p * x for p, x in zip(price, row, strict=True)) for row in features]
        schedules.append((j, direction, signs, charged))

    allowed = set(certificate["upper_neighbours"])
    require(len(allowed) == len(certificate["upper_neighbours"]) == 22
            and all(0 <= k < len(upper_dots) for k in allowed), "valid upper neighbor list")
    hall_rows = certificate["left_hall"]
    require(len(hall_rows) == len({i for i, _ in hall_rows}) == 117 + separate_halves, "distinct Hall rows")
    outside = defaultdict(list)
    for k, row in enumerate(upper_dots):
        if k not in allowed:
            outside[residue(row)].append(row)
    for i, price_ids in hall_rows:
        require(0 <= i < len(retained) and all(0 <= k < len(schedules) for k in price_ids), "valid Hall indices")
        cuts = []
        for price_id in price_ids:
            j, direction, signs, charged = schedules[price_id]
            bound = sum(max(0, direction * dot_change(retained[i], r, sign, copy) - cost)
                        for (r, sign, copy), cost in zip(signs, charged, strict=True))
            limit = lower_dots[i][j] + direction * 8 * (bound // 2)
            cuts.append((j, direction, limit))
        require(all(any(direction * (row[j] - limit) > 0 for j, direction, limit in cuts)
                    for row in outside[residue(lower_dots[i])]), "all edges out of Hall neighbor set are excluded")
    bound = len(retained) - len(hall_rows) + len(allowed)
    require(bound == certificate["bound"] == 1098 - separate_halves, "exact vector matching upper bound")
    scope = "fixed-fold" if separate_halves else "fixed-fold global-weight"
    print(f"n=2396 {scope} Hall bound: at most {bound}/{len(retained)} exact five-vectors; "
          f"{len(hall_rows)} lower indices, {len(allowed)} possible upper neighbors")


def check_factor_alternatives(cuts, factors, rows, lower, before_dots):
    half = BOTTOM // 2
    omitted = LOWER_OMISSIONS[1:]
    labels = [residue(before_dots[index]) for index in omitted]
    require(len(labels) == len(set(labels)) == 6, "distinct exact-factor residue labels")
    minus = [label for index, label in zip(omitted, labels, strict=True) if index >= half]
    plus = [label for index, label in zip(omitted, labels, strict=True) if index < half]
    require(len(minus) == 4 and len(plus) == 2, "two plus and four minus omission labels")
    shifts = [shift for shift in range(1 << WIDTH)
              if {tuple((value + 4 * (shift >> j & 1)) % 8 for j, value in enumerate(row))
                  for row in minus} == set(minus)]
    require(shifts == [0], "the four remaining minus labels have trivial offset stabilizer")
    beta_targets = [[tuple(-2 * value for value in row) for row in factor["factor"]] for factor in factors]
    require(all([residue(row) for row in beta] == labels for beta in beta_targets),
            "plus and minus residues force the archived ordering of all eight factors")

    folds, options = pair_data(rows)
    patterns = rows_from_columns(BOTTOM, [lower[index] for index in omitted])

    def features(u, v, r):
        x = [u >> j & 1 for j in range(WIDTH)]
        y = [v >> j & 1 for j in range(WIDTH)]
        first, second = patterns[r], patterns[r+half]
        return [a + b for a, b in zip(x, y, strict=True)] + [
            (1 - 2 * x[j]) * (2 * (first >> i & 1) - 1)
            + (1 - 2 * y[j]) * (2 * (second >> i & 1) - 1)
            for i in range(len(omitted)) for j in range(WIDTH)]

    target_weights = [sum(row >> j & 1 for row in rows) for j in range(WIDTH)]
    pairs = [[features(x, x ^ fold, r) for x in options[r]] for r, fold in enumerate(folds)]
    require([cut[0] for cut in cuts] == list(range(1, 8)), "all seven alternate factors")
    gaps = []
    for number, wanted, capacity, terms in cuts:
        target = target_weights + [value for row in beta_targets[number-1] for value in row]
        require(all(0 <= i < len(target) for i, _ in terms), "valid alternate-factor price indices")

        def score(feature):
            return sum(feature[i] * price for i, price in terms)

        require(score(target) == wanted and sum(max(map(score, local)) for local in pairs) == capacity
                and capacity < wanted, "exact local capacity separates an alternate factor")
        gaps.append(wanted - capacity)
    print(f"n=2396 fixed-fold alternate-factor cuts: seven exact separations, gaps {tuple(gaps)}")


def check_improved(upper, before, new, source, upper_dots, before_dots, retained):
    top, lower, _, lower_margin_rows = source
    before_rows, improved_rows = ([int(c, 32) for c in profile] for profile in (before, new))
    require(len(improved_rows) == len(before_rows) == BOTTOM, "each lower mask is encoded")
    require([x.bit_count() for x in improved_rows] == [x.bit_count() for x in lower_margin_rows], "lower row margins")
    half = BOTTOM // 2
    require((improved_rows[0], improved_rows[half]) == (before_rows[0], before_rows[half]), "same border pair")
    require(all(a ^ b == c ^ d for a, b, c, d in zip(improved_rows[:half], improved_rows[half:],
                                                  before_rows[:half], before_rows[half:], strict=True)),
            "same physical folded XOR at every index")
    old_cols, new_cols = decode(before), decode(new)
    require(all(a.bit_count() == b.bit_count() and (a >> half).bit_count() == (b >> half).bit_count()
                for a, b in zip(old_cols, new_cols, strict=True)), "same exact half column weights")
    require(all(a.bit_count() + b.bit_count() == ORDER // 2 for a, b in zip(upper, new_cols, strict=True)),
            "each exact full column weight")
    upper_gram = correlations(upper, upper, TOP)
    new_gram = correlations(new_cols, new_cols, BOTTOM)
    require(all(upper_gram[i][j] + new_gram[i][j] == ORDER * (i == j) for i in range(WIDTH) for j in range(WIDTH)),
            "all exact new/new orthogonalities")
    dots = correlations(lower, new_cols, BOTTOM)
    require(all(dots[i] == before_dots[i] for i in LOWER_OMISSIONS), "all 35 exact omitted projections")
    require(all(residue(a) == residue(b) for a, b in zip(dots, before_dots, strict=True)), "all indexed residues mod8")
    beta = [dots[i] for i in LOWER_OMISSIONS]
    require(not any(value for row in omitted_residual(correlations(top[1:3], upper, TOP), beta, upper_gram)
                    for value in row), "all 25 exact omitted Gram equalities")
    signed_dots = [[-x for x in dots[i]] for i in retained]
    require(low_high_moments(upper_dots) == low_high_moments(signed_dots), "mixed-bit moments")
    matches = []
    for modulus in (8, 16, 32, 64):
        a = Counter(tuple(x % modulus for x in row) for row in upper_dots)
        b = Counter(tuple(x % modulus for x in row) for row in signed_dots)
        matches.append(sum((a & b).values()))
    matches.append(sum((Counter(map(tuple, upper_dots)) & Counter(map(tuple, signed_dots))).values()))
    changes = sum(a != b for a, b in zip(improved_rows, before_rows, strict=True))
    require(matches == [1193, 921, 285, 45, 34], "recorded mixed-modulus match counts")
    print(f"n=2396 improved fixed-fold witness: {matches[-1]} exact five-vectors; joint matches {tuple(matches)}; "
          f"{changes} refined row masks")


def main():
    directory = Path(__file__).parent
    certificate = json.loads((directory / "exterior_fold_hall_certificate.json").read_text())
    previous = json.loads((directory / "exterior_mod16_invariant_witness.json").read_text())
    fixed = json.loads((directory / "exterior_fold_trade_exact_witness.json").read_text())
    factors = json.loads((directory / "exterior_exact_factor_witnesses.json").read_text())
    source = gram_fixture()
    top, lower, upper_margin_rows, lower_margin_rows = source
    require([int(c, 32).bit_count() for c in previous["upper"]] == [x.bit_count() for x in upper_margin_rows],
            "fixed upper row margins")
    upper = decode(previous["upper"])
    upper_dots = correlations(top[3:], upper, TOP)
    before_dots = correlations(lower, decode(fixed["lower"]), BOTTOM)
    require([before_dots[i] for i in LOWER_OMISSIONS[1:]]
            == [[-2 * value for value in row] for row in factors[7]["factor"]], "fixed omitted factor eight")
    retained = [i for i in range(BOTTOM) if i not in LOWER_OMISSIONS]
    rows = [int(c, 32) for c in fixed["lower"]]
    require([x.bit_count() for x in rows] == [x.bit_count() for x in lower_margin_rows], "fixed lower row margins")
    lower_dots = [[-x for x in before_dots[i]] for i in retained]
    check_hall(certificate, rows, upper_dots, lower_dots, retained, separate_halves=True)
    check_hall(certificate["global_weight"], rows, upper_dots, lower_dots, retained, separate_halves=False)
    check_factor_alternatives(certificate["alternate_factors"], factors, rows, lower, before_dots)
    check_improved(upper, fixed["lower"], certificate["improved_lower"], source, upper_dots, before_dots, retained)


if __name__ == "__main__":
    main()
