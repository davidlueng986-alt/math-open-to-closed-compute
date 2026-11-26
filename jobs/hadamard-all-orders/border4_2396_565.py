"""Reconstruct and verify the rank-one cross-star 565-shift order-2396 candidate."""

from border4_2396 import periodic
from border4_2396_changed_margins import CHANGED_MARGINS
from border4_2396_exact_negative import word
from border4_2396_nested import nested_negative_words
from border4_2396_shifted_tail import ALIGNMENT, N, compress, verify_lift

FIBRES = (6, 8, 11, 12)
SHORT_ORDER = 23
FIELD_FACTOR = 0xAE3
ORIGINAL_STAR = (361035, 290843, 2115171, 1646096)
SCALED_STAR = (2621938, 6454554, 129583, 4473283)
SHARED = 7841262
RATIO = 3270541
TAIL = 0xAF599A085AA3100885D00010880C0201000040200084442100000400201019E00400029C40
BAD_LAGS = (1, 6, 47, 109, 115, 119, 129, 149)


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def star(mask):
    return sum(1 << (-j % SHORT_ORDER) for j in indices(mask))


def multiply(a, b, cyclic):
    result = 0
    for j in indices(b):
        for i in indices(a):
            degree = (i + j) % SHORT_ORDER if cyclic else i + j
            result ^= 1 << degree
    return result


def field(mask):
    while mask.bit_length() > 11:
        mask ^= FIELD_FACTOR << (mask.bit_length() - 12)
    return mask


def short_fibres(masks):
    by_fibre = dict(zip(FIBRES, masks, strict=True))
    return sum(1 << i for i in range(N)
               if by_fibre.get(i % 13, 0) >> (i % SHORT_ORDER) & 1)


def switch(row, mask):
    assert all(row[i] for i in indices(mask))
    return tuple(-value if mask >> i & 1 else value for i, value in enumerate(row))


def reflect(row):
    return tuple(row[(ALIGNMENT - i) % N] for i in range(N))


def back_masks(front, shared=0):
    return tuple(shared ^ multiply(RATIO, a, True) for a in front)


def check_quotient_field() -> None:
    assert FIELD_FACTOR == sum(1 << j for j in (0, 1, 5, 6, 7, 9, 11))
    reverse_factor = sum(1 << (11 - j) for j in indices(FIELD_FACTOR))
    assert multiply(FIELD_FACTOR, reverse_factor, False) == (1 << 23) - 1
    assert pow(2, 11, 23) == 1 and 2 % 23 != 1
    assert sorted(min((a-b)%13,(b-a)%13) for i, a in enumerate(FIBRES)
                  for b in FIBRES[i+1:]) == list(range(1, 7))

    original_poles = tuple((field(a), field(star(a))) for a in ORIGINAL_STAR)
    scaled_poles = tuple((field(a), field(star(a))) for a in SCALED_STAR)
    assert original_poles == ((0, 941), (0, 285), (884, 415), (0, 567))
    assert scaled_poles == ((0, 547), (0, 111), (668, 59), (0, 67))
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            old = field(multiply(original_poles[i][1], original_poles[j][0], False))
            new = field(multiply(scaled_poles[i][1], scaled_poles[j][0], False))
            assert new == field(multiply(16, old, False))


def source_words():
    baseline = tuple(map(word, CHANGED_MARGINS))
    for row in baseline[:2]:
        assert all(row[i] for i in range(N) if i % 13 in FIBRES)
    u, v = (sum(1 << (i % SHORT_ORDER) for i in range(0, N, 13) if row[i] == 0)
            for row in baseline[:2])
    assert u == (v ^ 1) and u == star(u) and v == star(v)
    for row, holes in zip(baseline[:2], (u, v), strict=True):
        assert all(bool(value) == (i % 13 in FIBRES or
                                   not (holes >> (i % SHORT_ORDER) & 1))
                   for i, value in enumerate(row))
    for j in range(1, SHORT_ORDER):
        even = 1 | 1 << j
        assert multiply(v, multiply(RATIO, even, True), True) == multiply(u, even, True)

    check_quotient_field()
    assert star(SHARED) == SHARED and SHARED.bit_count() % 2 == 0
    assert all(a.bit_count() % 2 == 0 for a in ORIGINAL_STAR + SCALED_STAR)
    original_first = (switch(baseline[0], short_fibres(ORIGINAL_STAR)),
                      switch(baseline[1], short_fibres(back_masks(ORIGINAL_STAR))))
    assert tuple(map(compress, original_first)) == tuple(map(compress, baseline[:2]))
    first = (switch(original_first[0], short_fibres(SCALED_STAR)),
             switch(original_first[1], short_fibres(back_masks(SCALED_STAR, SHARED))))
    return first + (switch(baseline[2], TAIL), reflect(switch(reflect(baseline[3]), TAIL)))


def main():
    positive = source_words()
    negative = nested_negative_words()
    assert periodic(negative) == [599] + [0] * 298
    raw = periodic(positive)
    assert tuple(d for d in range(1, N // 2 + 1) if (raw[d] + 2) % 8) == BAD_LAGS
    symbols = {-1: "-", 0: ".", 1: "+"}
    patterns = tuple("".join(symbols[a] for a in row) for row in positive)
    verify_lift(patterns, negative, [0] * 7, 565, 113, 112, 846848)
    print("Exact C13: 565 of 597 original shifts modulo sixteen, 113 exactly -4.")
    print("Eight inverse raw failures:", BAD_LAGS)


if __name__ == "__main__":
    main()
