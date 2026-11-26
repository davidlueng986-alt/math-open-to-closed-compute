"""Replay anchored triples compatible with a large repeated-reserve pair."""

from collections import Counter
from hashlib import sha256
from itertools import combinations

from r_paley_anchored_triples import sign
from r_paley_large_lower import MASK, M, T, rectangle
from verify import goethals_seidel, length_299_words, rows_from_columns, verify_orthogonal


X = int(
    "595657999e7657dc83a9c7802043e62aa804c056e11eb7b90a9bede5e52d4a76a725"
    "385db84bfd9fd48f70a4237ab2090d0d695ac4ac6d63d123da6a9e8666189a8237c5"
    "6387fdfbc19d566b629a44a494805dc36d9ca6ea6ac7624318549a90eb7b6aa7945c"
    "c7549c59238c9ba2db6a06aa484a3da9b579cf6e472a6a26b1924f117fb5b6bf69ae"
    "4a6d4925d13671db2e36a8e62eb", 16,
)
R, S, G, GAMMA = 764, 933, 161, 127
FLIPS = (
    (G, (R,)), (G, (S,)), (322, (R, S, 711)), (346, (R, S, 466)),
    (424, (R, S, 1028)), (157, (379,)), (82, (248,)), (1055, (R, S, 636)),
)


def verify():
    source = goethals_seidel(length_299_words())
    rows = rows_from_columns(M, source)
    disagreement = rows[R] ^ rows[S]
    if sign(disagreement, G) > 0:
        disagreement ^= MASK
    assert disagreement.bit_count() == T - 1 and disagreement & X == disagreement
    holes = X ^ disagreement
    e, f = (j for j in range(M) if holes >> j & 1)
    assert GAMMA in (e, f) and not X >> G & 1

    counts = Counter()
    candidates = {}
    unused = (MASK ^ X) ^ (1 << G)
    for p, row in enumerate(rows):
        if p in (R, S):
            continue
        pattern = MASK ^ rows[R] ^ row
        agreement = MASK ^ disagreement
        assert (pattern & agreement).bit_count() == (T - 1) // 2
        a = sign(pattern, e) + sign(pattern, f) - sign(pattern, G)
        triple = abs(a) == 3
        if triple:
            a = sign(pattern, G)
        choices = unused & (pattern if a > 0 else pattern ^ MASK)
        counts[triple] += choices.bit_count()
        candidates[p] = triple, choices
    assert counts == {False: 266116, True: 89102}
    assert sum(triple for triple, _ in candidates.values()) == 299
    for h, support in FLIPS[2:]:
        triple, choices = candidates[support[-1]]
        assert len(support) == (3 if triple else 1)
        assert choices >> h & 1

    selected = tuple(j for j in range(M) if X >> j & 1 and j != GAMMA)
    columns, lower = rectangle(source, selected, GAMMA, FLIPS)
    pair_dots = Counter(M - 2 * (a ^ b).bit_count() for a, b in combinations(lower, 2))
    assert pair_dots == {1192: 1, -8: 2, -4: 15, 0: 10}
    assert len(columns) == 1208 and verify_orthogonal(4 * T, columns) == 729028
    digest = sha256(b"".join(word.to_bytes(300, "little") for word in columns)).hexdigest()
    assert digest == "0ebba91f55a8a331d18699fe6b070090a259e383304c81768753f63b82bf2087"
    print("Giant pair: 89102 compatible triples and 266116 compatible singles")
    print("Hadamard 2396 × 1208: 729028 zero products, lower dots 1192 once, -8 twice, -4 fifteen times")


if __name__ == "__main__":
    verify()
