"""Replay two restrictions for combining a periodic far word with small flips."""

from itertools import combinations

from r_paley_far_periodic import raw_word, row_fibres
from verify import goethals_seidel, length_299_words, rows_from_columns


M = 1196


def verify_fibre_coverage(rows, fibres):
    # Three guard bits separate each pair of adjacent 13-coordinate fibres.
    packed = [
        sum(sum((row >> j & 1) << k for k, j in enumerate(fibre)) << (16 * i)
            for i, fibre in enumerate(fibres))
        for row in rows
    ]
    starts = sum(1 << (16 * i) for i in range(len(fibres)))
    mask = starts * ((1 << 13) - 1)

    def cover(word):
        for shift in (8, 4, 2, 1):
            word |= word >> shift
        return (word & starts).bit_count()

    minimum, attaining = len(fibres), 0
    for left, right in combinations(packed, 2):
        different = left ^ right
        for word in (different, different ^ mask):
            count = cover(word)
            if count < minimum:
                minimum, attaining = count, 1
            elif count == minimum:
                attaining += 1
    assert (minimum, attaining) == (68, 8)
    print("Periodic support: each signed disagreement word meets at least 68 column fibres")


def verify_restricted_gram(source, rows, fibres):
    far = raw_word(source, fibres)
    eligible = sum((abs(M - 2 * (far ^ col).bit_count()) == 2) << j
                   for j, col in enumerate(source))
    assert eligible.bit_count() == 637
    restricted = [row & eligible for row in rows]
    high = []
    maximum = 0
    for i, j in combinations(range(M), 2):
        value = abs(637 - 2 * (restricted[i] ^ restricted[j]).bit_count())
        maximum = max(maximum, value)
        if value > 143:
            high.append((i, j, value))
    assert maximum == 181 and high == [
        (357, 1007, 181), (409, 955, 175), (487, 1137, 175), (539, 1085, 181),
    ]
    assert len({r for i, j, _ in high for r in (i, j)}) == 8
    assert (637 - 181 - 2 * 143 + 3) // 4 == 43 > 637 - 600
    print("Known far word: every signed three-row sum has at least 43 invalid coordinates in E637")


def verify():
    source = goethals_seidel(length_299_words())
    rows = rows_from_columns(M, source)
    fibres = row_fibres()
    assert len(fibres) == 92 and all(len(fibre) == 13 for fibre in fibres)
    verify_fibre_coverage(rows, fibres)
    verify_restricted_gram(source, rows, fibres)


if __name__ == "__main__":
    verify()
