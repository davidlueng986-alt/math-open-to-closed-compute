"""Replay a five-column stack with exact row margins and omitted Gram equality."""

from collections import Counter, defaultdict

from five_column_constraints import (
    BOTTOM,
    LOWER_OMISSIONS,
    ORDER,
    TOP,
    WIDTH,
    correlations,
    exterior_sources,
    positive_columns,
    require,
    rows_from_columns,
)


# (Positive mask in omitted columns, negative mask in new columns, count).
UPPER_COUNTS = (
    (1, 13, 108), (1, 22, 15), (1, 28, 176),
    (3, 5, 75), (3, 9, 59), (3, 12, 1), (3, 17, 135), (3, 20, 29),
    (5, 3, 1), (5, 6, 138), (5, 10, 122), (5, 12, 29), (5, 17, 8), (5, 18, 1),
    (7, 1, 45), (7, 2, 73), (7, 4, 57), (7, 8, 54), (7, 16, 69),
)
HALF_BETA = (
    (67, 80, 122, 171, 159),
    (11, 254, 92, 99, 143),
    (181, 78, 270, 59, 11),
    (87, 102, 56, 265, 89),
    (87, 232, 102, 97, 81),
    (305, 72, 132, -51, 141),
)


LOWER_COUNTS = (
    (0, 31, 1), (2, 31, 25), (4, 31, 25), (6, 23, 24),
    (8, 31, 25), (10, 27, 12), (12, 23, 10), (12, 27, 10),
    (14, 19, 18), (16, 31, 26), (18, 15, 12), (18, 27, 6),
    (20, 23, 13), (20, 27, 1), (22, 11, 12), (22, 21, 5),
    (24, 27, 20), (26, 7, 9), (26, 22, 8), (28, 11, 10),
    (28, 25, 11), (30, 3, 15), (30, 6, 2), (32, 31, 20),
    (34, 27, 18), (36, 23, 1), (36, 27, 15), (38, 21, 21),
    (40, 29, 1), (40, 30, 17), (42, 7, 12), (42, 14, 2),
    (42, 25, 4), (42, 26, 5), (44, 13, 19), (46, 3, 9),
    (46, 5, 6), (48, 23, 20), (50, 14, 1), (50, 19, 15),
    (52, 21, 18), (54, 5, 20), (54, 20, 1), (56, 19, 13),
    (56, 22, 6), (56, 28, 1), (58, 18, 21), (60, 3, 1),
    (60, 17, 16), (62, 1, 17), (64, 31, 20), (66, 15, 17),
    (66, 27, 4), (68, 15, 17), (70, 11, 10), (70, 19, 7),
    (72, 30, 20), (74, 11, 16), (76, 26, 18), (78, 18, 20),
    (78, 20, 1), (80, 23, 11), (80, 30, 7), (82, 7, 9),
    (82, 22, 14), (84, 11, 7), (84, 22, 12), (86, 6, 3),
    (86, 12, 12), (88, 11, 12), (88, 22, 8), (90, 18, 18),
    (92, 3, 6), (92, 24, 10), (94, 1, 1), (94, 8, 7),
    (94, 16, 13), (96, 27, 19), (96, 30, 1), (98, 11, 17),
    (100, 7, 3), (100, 26, 3), (100, 28, 15), (102, 6, 8),
    (102, 9, 9), (104, 26, 26), (106, 24, 18), (108, 9, 11),
    (108, 17, 1), (108, 20, 2), (110, 8, 17), (112, 7, 25),
    (114, 6, 12), (116, 5, 1), (116, 24, 19), (118, 2, 2),
    (118, 8, 15), (118, 16, 1), (120, 12, 1), (122, 2, 1),
    (122, 16, 24), (124, 1, 8), (124, 2, 15), (124, 8, 2),
    (126, 0, 24),
)


# Alternate physical placements of the same grouped counts, one base-32 mask per row.
MOD8_UPPER_ROWS = (
    "0kka4kkhsssss4h4hgkhss8hss8kh8khgkhgcs8csgkcc2kkkkkkkc4cs86gcmss4kkc2cgkkkcs8cga"
    "8k64kkkkkcgc2kh9css855h9csgc8cs8hcs8hcgc86s4csgc2h964hcsss4hc4c45asg968c4hag6s46"
    "s4956sg96sss8646ss49h9h68h6s8asss26s4c8has45hh6ss86ssgh6ga2asss46s46s2ag68h96sga"
    "4assg56s46s2h964asg6g9hha496g59agam4h6g6g5assg9asg6sgh6s8hassa98sigs65hgsss6gsss"
    "s68sagsss6hgsssahhh8ss6gss646hgsag6hhhhga8s6h264ss62a5g6hhh4sssa2ss6h4a5h5gsssa5"
    "9hh4ah8ssah9hh52ah9865555h8sa8sahhgah8sssssa4ss6546h8sagsa4sssma4a8sssss6g6586gs"
    "scgsa95462ss6gs68sahh864s69hgs6h5g6h4sss6hhga92a94ah86h8a4ss6g68s6h9hgah54ssah4d"
    "ahhg64agssssc86hh54s6g6954ags6h592ah8s5h8ss6h95hga4a5h4sa54ssa8sah9g64s698sa8sah"
    "5gs65864akgs6hhga86gagss6g6ga864ss64a46gs6g6hhgsssssssa58ss6h2sssa8a2ssss698sma2"
    "mma2mmdmah2sa2a2a5586995552mmsm62m692a26hh262ahh2a92a4m626262a52a2a2sa9g65955h2d"
    "68dda4dah2a552a9hh52dda5262d62652ddddda2dd62dddddddd6552a2a2agdah2c5h26268da26h4"
    "dd65h2d692dda4dd6a4ddd62ah2dd6hgd6262a952652da99hh59hh2ddd6862dddddddd68dah2a92d"
    "ah2d62626h2ah2da526h2dda2651dda51dd61dddddd6h916hhhh5h1a91a51mdd61dda9h1dda161a5"
    "h516161a9161da9h5hh51da95h1dd6h51dddddah591d6h955h1a16h951dd65hh5hh1dda91dahh169"
    "161dd6h1d6951dsdd616h559h1ddddah1a1a916h1d61da1a1da1dah1ah991ddd61d6951d3h1d"
)
MOD8_LOWER_ROWS = (
    "vrebgkigv9iiomiqv851ommvvj0qmo7rmbmjqrrgj51qmsnm81iijiqjkonks6m7l9jh6ohvjidmj5i0"
    "obqiqpjpmfflhvfvp0m6rmmjggvldfqncuo9hmlro88dvq6uvroruvon8gdn8rgiqvhvlgv9gr0gqnmu"
    "c5bgi8vnp7nmovsrluvmr0julvv8vjdco98nbbqrnb62ki1rvjoovipqrfbdlmbmuvrqjgdrcmf05qnv"
    "l8unih8i5mfi6rrp0juvunpvbpr9lmogu5rrrvvmdnsnog3hv8ghvfolrrqurbr3ulqv1giulvomnuvm"
    "io2b88oprluvuf0mcvvr9jjgdvvlnp7rlqvnrsrjrvii3qvnjubgrvvqrihu530r7ripvv61qmrmuvcq"
    "vb1grvrirjpfrli28gi2fsbii1imi2ln5qvmvr7rrvciv8orv7or2oj3pnmvjh919sslmrunp7bufqju"
    "753v5obbeml7rl9jdvnbvcrjvvrl0oqbi0idb2vnm9rfsnm9bn5mor8uvr0m2jgumbqoo7vvrfr9rgib"
    "srvnvbhrblpvo2nrsl3gqn7oovmvvmbnv9jnvvrvcomjv5fl73f5r7fvgbcbfbvjqbnmbnviv8vbvi6v"
    "8cbldb0vjb5r85m8nn0nbrvvq38frfnj1rm78c5nr87f7sbsdhh8f2hg7nvro7vbll78miv93nn3fd8r"
    "rjbmglrng6rinbn0lvmujrj5lgfb8v73v6nvv0vu3cjlrb70sv0bf7boqrjdon8nqqgv2bb3r3vu8jvo"
    "986virb671rngr7vrijbqd7bn2iv1vbr3vin6vubqjn05fjr6vi56oo7n2nqu0sq7sonq7flnio3rqj7"
    "bub0fl6fjjlfqhn8oivu3766n8v2bl5nqgfvuu27ffv8bbf7ognjuinv37g6n12vbq2q0qvr8lbuov31"
    "og556l2u1n7vo1gli5fui6nrvirqqjrbv7rduq3v11blrqi5r1qirgfvjvfvhb7f5bfbfvqui77773vr"
    "313f7jrr1vnivnb670vqbf3bnbbgb6n07v8novbnvi67ifv77v87r8nbbju8735b7q98nfl7rnrb7vju"
    "d3rhbud3v9ibrrjnbonbvbln7elnnv1133inivrvbrjub7fiv87gfvurb16vl9vrnj77j7vtb3v911rq"
)


def expand_profile(omitted_patterns, counts):
    groups = {pattern: [] for pattern in omitted_patterns}
    for omitted, negative, count in counts:
        require(count > 0 and omitted in groups, "valid grouped row count")
        groups[omitted].extend([negative] * count)
    require({pattern: len(group) for pattern, group in groups.items()}
            == Counter(omitted_patterns), "grouped counts fit omitted row patterns")
    return [groups[pattern].pop() for pattern in omitted_patterns]


def gram_fixture():
    """Return the normalized factors and five candidate sign rows for each half."""
    top, lower = exterior_sources()
    omitted_top = rows_from_columns(TOP, top[:3])
    omitted_lower = rows_from_columns(BOTTOM, [lower[j] for j in LOWER_OMISSIONS])
    top_rows = [0] + expand_profile(omitted_top[1:], UPPER_COUNTS)
    lower_rows = expand_profile(omitted_lower, LOWER_COUNTS)

    require(omitted_top[0] == 7 and all(mask.bit_count() == 4 - omitted.bit_count()
            for mask, omitted in zip(top_rows[1:], omitted_top[1:], strict=True)),
            "upper row margins")
    require(omitted_lower[0] == 0 and lower_rows[0] == 31 and all(
        mask.bit_count() == 6 - omitted.bit_count()
        for mask, omitted in zip(lower_rows[1:], omitted_lower[1:], strict=True)),
        "lower row margins")
    return top, lower, top_rows, lower_rows


def mod8_fixture(top, lower, top_rows, lower_rows):
    alternate_top = [int(symbol, 32) for symbol in MOD8_UPPER_ROWS]
    alternate_lower = [int(symbol, 32) for symbol in MOD8_LOWER_ROWS]
    require(alternate_top[0] == 0 and alternate_lower[0] == 31, "specified border signs")
    omitted_top = rows_from_columns(TOP, top[:3])
    omitted_lower = rows_from_columns(BOTTOM, [lower[j] for j in LOWER_OMISSIONS])
    require(Counter(zip(omitted_top, alternate_top, strict=True))
            == Counter(zip(omitted_top, top_rows, strict=True)), "upper joint counts preserved")
    require(Counter(zip(omitted_lower, alternate_lower, strict=True))
            == Counter(zip(omitted_lower, lower_rows, strict=True)), "lower joint counts preserved")
    return positive_columns(alternate_top), positive_columns(alternate_lower)


def match_by_residues(upper_dots, negative_lower_dots,
                      levels=((4096, 8), (64, 20), (32, 281), (16, 887), (8, 1193))):
    """Pair within exact fibers, then merge fibers at successively smaller moduli."""
    pending_upper = list(range(len(upper_dots)))
    pending_lower = list(range(len(negative_lower_dots)))
    pairs = []
    for modulus, expected in levels:
        buckets = defaultdict(list)
        for index in pending_lower:
            buckets[tuple(value % modulus for value in negative_lower_dots[index])].append(index)
        unmatched_upper = []
        used_lower = set()
        for index in pending_upper:
            bucket = buckets[tuple(value % modulus for value in upper_dots[index])]
            if bucket:
                lower_index = bucket.pop()
                pairs.append((index, lower_index))
                used_lower.add(lower_index)
            else:
                unmatched_upper.append(index)
        require(len(pairs) == expected, f"paired vectors modulo {modulus}")
        pending_upper = unmatched_upper
        pending_lower = [index for index in pending_lower if index not in used_lower]
    require(not pending_upper and not pending_lower, "all retained columns paired")
    return pairs


def main():
    top, lower, top_rows, lower_rows = gram_fixture()
    new_top, new_lower = positive_columns(top_rows), positive_columns(lower_rows)
    require(all(a.bit_count() + b.bit_count() == ORDER // 2
                for a, b in zip(new_top, new_lower, strict=True)), "new columns balance")

    alpha = correlations(top[1:3], new_top, TOP)
    beta = correlations([lower[j] for j in LOWER_OMISSIONS[1:]], new_lower, BOTTOM)
    require(alpha == [[-394, 408, 608, 642, -66], [646, -640, 360, 278, 554]],
            "actual upper omitted projections")
    require(beta == [[2 * value for value in row] for row in HALF_BETA],
            "actual lower omitted projections")
    require(all(sum(row) == ORDER // 2 for row in alpha + beta), "omitted projection sums")

    gram = correlations(new_top, new_top, TOP)
    gram_lower = correlations(new_lower, new_lower, BOTTOM)
    require(all(gram[i][j] + gram_lower[i][j] == ORDER * (i == j)
                for i in range(WIDTH) for j in range(WIDTH)), "new columns are orthogonal")
    require(all(
        sum(row[i] * row[j] for row in beta) - sum(row[i] * row[j] for row in alpha)
        == ORDER * (BOTTOM * (i == j) - gram[i][j])
        for i in range(WIDTH) for j in range(WIDTH)), "all 25 omitted Gram entries")

    retained_lower = [column for j, column in enumerate(lower) if j not in LOWER_OMISSIONS]
    rho = correlations(top[3:], new_top, TOP)
    sigma = correlations(retained_lower, new_lower, BOTTOM)
    mixed = sum(x + y == 0 for a, b in zip(rho, sigma, strict=True)
                for x, y in zip(a, b, strict=True))
    require(mixed == 247, "indexed pairing mixed cancellation count")
    print("  five-column fixture: row and column balance, new/new orthogonality, omitted Gram equality")
    print(f"  indexed pairing cancels {mixed}/{len(rho) * WIDTH} mixed inner products")

    alt_top, alt_lower = mod8_fixture(top, lower, top_rows, lower_rows)
    upper_dots = correlations(top[3:], alt_top, TOP)
    negative_lower_dots = [[-value for value in row]
                           for row in correlations(retained_lower, alt_lower, BOTTOM)]
    pairs = match_by_residues(upper_dots, negative_lower_dots)
    mixed_dots = [x - y for i, j in pairs
                  for x, y in zip(upper_dots[i], negative_lower_dots[j], strict=True)]
    require(all(value % 8 == 0 for value in mixed_dots), "all mixed dots vanish modulo 8")
    require(mixed_dots.count(0) == 1101, "exact mixed zero count with modular pairing")
    print("  same grouped profile: all 1193 vectors paired modulo 8, including 887 modulo 16 and 281 modulo 32")
    print(f"  modular pairing cancels {mixed_dots.count(0)}/{len(mixed_dots)} mixed inner products exactly")


if __name__ == "__main__":
    main()
