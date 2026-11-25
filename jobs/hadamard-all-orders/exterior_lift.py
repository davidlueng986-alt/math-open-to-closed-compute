"""Exact upper inverse and the lower Paley code for lifting an exterior stack."""
from collections import Counter, defaultdict
import json
from pathlib import Path

from five_column_constraints import BOTTOM, LOWER_OMISSIONS, TOP, correlations, positive_columns
from five_column_gram import gram_fixture, match_by_residues, mod8_fixture
from verify import paley, require, rows_from_columns


def upper_binary_rows(top):
    # Keep core columns and rows only. A bit of one denotes a negative sign.
    core_mask = (1 << (len(top) - 1)) - 1
    return [row ^ core_mask for row in rows_from_columns(len(top), top[1:])[1:]]


def inverse_residues(binary_rows, weight, dots, modulus):
    """Recover the unique upper candidate modulo modulus/4 for odd core multiplier."""
    require(modulus >= 8 and (modulus & (modulus - 1)) == 0, "nontrivial sign inner-product modulus")
    require(len(dots) == len(binary_rows) and all((dot + 2 * weight) % 4 == 0 for dot in dots),
            "prescribed residues agree modulo four")
    reduced = modulus // 4
    scale = pow((len(binary_rows) + 1) // 4, -1, reduced)
    buckets = defaultdict(int)
    for j, dot in enumerate(dots):
        residue = ((dot + 2 * weight) // 4) % reduced
        buckets[residue] |= 1 << j
    return [(scale * sum(value * (row & mask).bit_count() for value, mask in buckets.items())
             - weight) % reduced for row in binary_rows]


def check_joint_fixture():
    top, lower, top_rows, lower_rows = gram_fixture()
    new_top, new_lower = mod8_fixture(top, lower, top_rows, lower_rows)
    lower_retained = [column for j, column in enumerate(lower) if j not in LOWER_OMISSIONS]
    actual = correlations(top[1:], new_top, TOP)
    upper_retained = actual[2:]
    target = [[-value for value in row]
              for row in correlations(lower_retained, new_lower, BOTTOM)]
    pairing = dict(match_by_residues(upper_retained, target))
    binary_rows = upper_binary_rows(top)
    errors = []
    scalar_unmatched = []
    for j, column in enumerate(new_top):
        weight = TOP - column.bit_count()
        actual_inner_products = [values[j] for values in actual]
        expected = [1 - (column >> i & 1) for i in range(1, TOP)]
        require(inverse_residues(binary_rows, weight, actual_inner_products, 16) == expected,
                "upper inverse recovers the archived column")
        requested = actual_inner_products[:2] + [target[pairing[i]][j] for i in range(len(target))]
        require(inverse_residues(binary_rows, weight, requested, 8) == expected,
                "every paired residue gives the original binary column modulo two")
        lifted = inverse_residues(binary_rows, weight, requested, 16)
        errors.append(sum(value >= 2 for value in lifted))
        upper_hist = Counter(row[j] % 16 for row in upper_retained)
        lower_hist = Counter(row[j] % 16 for row in target)
        scalar_unmatched.append(len(target) - sum((upper_hist & lower_hist).values()))
    require(errors == [606, 620, 610, 598, 606], "no candidate upper column at the archived pairing")
    require(scalar_unmatched == [30, 20, 22, 32, 16], "all fixed new columns must change")
    print(f"n=2396: invalid upper bits at modulus 16 under the archived pairing: {errors}")
    print(f"n=2396: each fixed new column has unmatched scalar residues modulo 16: {scalar_unmatched}")
    return top, lower, new_top, new_lower


def check_paley_code():
    words = paley(599)
    require(all(word.bit_count() % 4 == 0 for word in words), "doubly even generators")
    require(all((word & other).bit_count() % 2 == 0
                for j, word in enumerate(words) for other in words[:j + 1]), "self-orthogonality")
    pivots = {}
    for word in words:
        while word:
            lead = word.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = word
                break
            word ^= pivots[lead]
    require(len(pivots) == 300, "Paley positive columns span a self-dual code")
    bases = Counter(j % 600 for j in range(BOTTOM) if j not in LOWER_OMISSIONS)
    require(Counter(bases.values()) == {1: 7, 2: 593}, "every base label and the copy structure")
    require(pow(2, 299, 599) == 1 and pow(598, 299, 599) == 598, "multipliers 2 and -1")
    require(24**2 - 24 + 1 < 599 <= 25**2 - 25 + 1, "punctured square-root bound")
    print("n=2396: lower residue fiber uses a doubly even self-dual [600,300] Paley code")


def check_new_placements(top, lower, original_top, original_lower):
    payload = json.loads(Path(__file__).with_name("exterior_lift_witnesses.json").read_text())
    kept_bottom = [column for i, column in enumerate(lower) if i not in LOWER_OMISSIONS]
    omitted_top = top[:3]
    omitted_bottom = [lower[i] for i in LOWER_OMISSIONS]
    old_lower_dots = correlations(kept_bottom, original_lower, BOTTOM)
    variants = [
        ("cross-omission swaps", original_top, positive_columns([int(s, 32) for s in payload["indexed_lower"]]),
         ((4096, 9), (64, 23), (32, 282), (16, 954), (8, 1193))),
        ("combined swaps", positive_columns([int(s, 32) for s in payload["hybrid_upper"]]),
         positive_columns([int(s, 32) for s in payload["hybrid_lower"]]),
         ((4096, 3), (64, 19), (32, 296), (16, 994), (8, 1193))),
    ]
    for name, upper, bottom, levels in variants:
        for length, new, original, omitted in (
            (TOP, upper, original_top, omitted_top), (BOTTOM, bottom, original_lower, omitted_bottom)
        ):
            rows = rows_from_columns(length, new)
            old_rows = rows_from_columns(length, original)
            require(rows[0] == old_rows[0], "border signs stay normalized")
            require([row.bit_count() for row in rows] == [row.bit_count() for row in old_rows],
                    "all prescribed row margins")
            require(correlations(omitted, new, length) == correlations(omitted, original, length),
                    "all exact omitted projections, including constant-column weights")
            require(correlations(new, new, length) == correlations(original, original, length),
                    "each half of the exact new/new Gram")
            if name == "cross-omission swaps" and length == BOTTOM:
                omitted_rows = rows_from_columns(length, omitted)
                changed_group_counts = sum((Counter(zip(omitted_rows, old_rows)) -
                                       Counter(zip(omitted_rows, rows))).values())
                require(changed_group_counts == 44, "this trade genuinely changes the grouped profile")
        upper_dots = correlations(top[3:], upper, TOP)
        lower_dots = correlations(kept_bottom, bottom, BOTTOM)
        if name == "cross-omission swaps":
            require(all((a - b) % 8 == 0 for actual, previous in zip(lower_dots, old_lower_dots, strict=True)
                        for a, b in zip(actual, previous, strict=True)), "every indexed lower residue stays fixed")
        pairs = match_by_residues(upper_dots, [[-x for x in row] for row in lower_dots], levels=levels)
        exact_scalars = sum(a + b == 0 for i, j in pairs
                            for a, b in zip(upper_dots[i], lower_dots[j], strict=True))
        require(exact_scalars == 1131, "exact mixed zeros under the deterministic pairing")
        print(f"n=2396: {name}: {levels[3][1]} full vectors modulo 16, all 1193 modulo 8, "
              f"{exact_scalars} individual exact mixed zeros")


if __name__ == "__main__":
    archive = check_joint_fixture()
    check_paley_code()
    check_new_placements(*archive)
