"""Exact norm-599 four-word negative projection on C299, and its fixed positive supports."""

from sys import argv

from border4_2396 import periodic
from t599_length_change import aperiodic


POSITIVE_MOD4_C13 = (
    (
        "..+...+.+.+-+....--+++-.--......---..++.-+-+--.--.+-....+.-."
        "-..++--+-..-.+..--.-....-.-+--++..+..+.-..++.....++-++++++.."
        "...+.+..--..---+-++.-++.....--.-..-+-+---.-++..-+..-...+.-++"
        "+-++..-.-.-..+-......++--++-.+....+.++.-+...+----+..+-......"
        "+.-..++-+-----.+..--...-..-.+.+++-+-..-+.+..+++.....+++----"
    ),
    (
        "......+.-..+-..+-+-+--+.--......+.++.++++-++--.-..++......-."
        "-+++++--+..-.+..++...-..-++-+--+.....+.-..--+..-+++-++-++..."
        "...-.+.++++---+----..+-......+-+.-+++----.+.-..--....+.+--+-"
        "+-++....-.-..-+.-..+--+--++-......-.+..-+.+-+--+--..--......"
        "+.+..-++---+++.+..+-.....--.++--+++-...+.-..--..-..++--++--"
    ),
    (
        ".--.......++.......++.......--.......--.......-+......--++-+"
        "+--.+...--...+-.......-...-+...+...+-...-...+-..+++-+-++-++-"
        "+--++-.+...+-...-...++...+-.......-+......-+--+-+---++-+--+-"
        ".-+.......+-.......-+.......+...+-...--......++----+++.+...+"
        "+...-...+-...-...--...+...++...+...++...-...--..+-++-+---++"
    ),
    (
        "..+-...+...+-...-...++...-...-+...+...++...+...-+...+.-+----"
        "-++......++...-+...+.......--.......--.......--.-----+-----+"
        "+--+++......+-.......++...-+...-...-+...+.++--+-+--+-++-+--+"
        "..++...-...++...-...-+...-.......++...-+...+.++-+++--+......"
        "--.......+-.......--.......+-.......++.......++.+-----+++--"
    ),
)

REFINED_LAST_WORDS = (
    (
        ".+-.......+-.......-+.......--.......+-.......--......-++-+-"
        "++-.+...--...++.......+...--...+...--...-...--..++--+--+++-+"
        "++++++.-...++...-...++...-+.......-+......++---++++---+-+--+"
        ".++.......+-.......--.......+...++...-+......+-++-----.+...+"
        "+...-...--...+...+-...+...--...+...+-...+...+-..--++----+--"
    ),
    (
        "..++...-...--...-...--...-...--...-...+-...+...-+...+.+-+--+"
        "+-+......-+...++...+.......+-.......--.......-+.++-++-++-+++"
        "-+-++-......+-.......--...-+...-...++...-.-+-+---+----+-++-+"
        "..+-...-...+-...-...++...+.......-+...-+...+.+------++......"
        "+-.......++.......--.......++.......-+.......+-.-++--++++-+"
    ),
)

POSITIVE_MOD8 = (
    (
        "..+...-.-.--+....----+-.-+......--+..+-.-++---.--.++....-.+."
        "+..-+----..+.+..--.-....-.------..-..-.+..++.....++++++-++.."
        "...+.+..++..++-++--.++-.....-+.-..-+-++--.++-..++..+...+.+-+"
        "----..-.-.-..--......++-+-++.-....+.-+.-+...++++--..++......"
        "+.-..-++++-++-.-..--...+..+.+.-++-+-..+-.-..-++.....+--++-+"
    ),
    (
        "......+.+..++..-+-++-+-.--......+.-+.+-+---++-.-..++......-."
        "+-++-+-++..-.+..++...+..+--+-++-.....-.-..-++..++++----++..."
        "...+.+.--++-+-+-+--..+-......+--.--+-+-++.+.+..+-....-.--+--"
        "+---....+.+..++.+..-+---++-+......-.+..++.-++++---..-+......"
        "-.-..+--+-+---.-..-+.....--.+--+-+++...-.-..--..+..+---+-++"
    ),
    (
        ".++.......++.......+-.......--.......--.......-+......+++---"
        "+--.-...-+...++.......+...--...-...++...-...++..++++-+--++-+"
        "-+--+-.-...+-...-...++...-+.......-+......-+-----++---++-+--"
        ".++.......++.......+-.......-...-+...--......--++-+-++.+...-"
        "+...-...++...-...++...-...-+...-...--...-...--..+--++++-+++"
    ),
    (
        "..+-...+...-+...+...+-...+...+-...+...-+...+...--...+.-+++-+"
        "+--......++...+-...-.......++.......+-.......-+.-++---++-++-"
        "++-+++......+-.......--...-+...-...-+...-.+++--+-+--+--+---+"
        "..-+...-...-+...+...++...+.......-+...++...-.++--+--+-......"
        "--.......+-.......--.......--.......++.......--.+-+-+--+---"
    ),
)


def word(text):
    return tuple({"+": 1, "-": -1, ".": 0}[symbol] for symbol in text)


def negative_words():
    weighing13 = word("--++-+.+.++..")
    pair23 = tuple(map(word, ("-+.-+++--+.+++++-......", "+++-++-+---+.+-........")))
    assert periodic((weighing13,)) == [9] + [0] * 12
    assert periodic(pair23) == [29] + [0] * 22
    first = tuple(tuple(weighing13[i % 13] * a[i % 23] for i in range(299)) for a in pair23)
    assert periodic(first) == [261] + [0] * 298

    a, b = map(word, ("-.+++..+-", "-+++-+..+"))
    assert aperiodic((a, b)) == [13] + [0] * 8
    left_a, left_b = (0,) * 7 + a, b + (0,) * 7
    assert all(not (x and y) for x, y in zip(left_a, left_b, strict=True))
    padded_size = len(left_a)
    assert aperiodic((left_a, left_b)) == [13] + [0] * (padded_size - 1)
    e = tuple(x * u + y * v for x, y in zip(left_a, left_b, strict=True)
              for u, v in zip(a, b[::-1], strict=True))
    f = tuple(x * u - y * v for x, y in zip(left_a, left_b, strict=True)
              for u, v in zip(b, a[::-1], strict=True))
    assert len(e) == len(f) == 144
    assert aperiodic((e, f)) == [169] + [0] * 143
    third = e + f[::-1]
    fourth = f + tuple(-x for x in reversed(e))
    assert aperiodic((third, fourth)) == [338] + [0] * 287
    second = tuple(a + (0,) * (299 - len(a)) for a in (third, fourth))
    assert periodic(second) == [338] + [0] * 298

    final = first + second
    assert all(set(a) <= {-1,0,1} for a in final)
    assert periodic(final) == [599] + [0] * 298
    assert tuple(map(sum, final)) == (15, 6, 13, -13)
    return final


def verify_positive(positive, negative, inverse_pairs, modulus, exact_quotient):
    assert all(len(row) == 299 for row in positive)
    assert all(s * s + t * t == 1 for a, b in zip(positive, negative, strict=True)
               for s, t in zip(a, b, strict=True))
    assert tuple(map(sum, positive)) == (0, 1, 0, 0)
    corr = periodic(positive)
    assert corr[0] == 597
    assert all((value + 2) % modulus == 0 for value in corr[1:])
    assert sum(value == -2 for value in corr[1:150]) == inverse_pairs
    compressed = tuple(tuple(sum(row[r::13]) for r in range(13)) for row in positive)
    if not exact_quotient:
        quotient_corr = periodic(compressed)
        assert max(abs(a - b) for a, b in zip(quotient_corr, [553] + [-46] * 12, strict=True)) == 168
        return
    assert periodic(compressed) == [553] + [-46] * 12
    buckets = [
        [lag for lag in range(1, 150) if min(lag % 13, (-lag) % 13) == residue]
        for residue in range(7)
    ]
    assert list(map(len, buckets)) == [11] + [23] * 6
    assert all(sum(corr[lag] + 2 for lag in bucket) == 0 for bucket in buckets)
    assert sum(len(bucket) - 1 for bucket in buckets) == 142


def support_rank(supports):
    """Rank of the off-origin mod-four rows and prescribed row-sum parities."""
    length = len(supports[0])
    full = (1 << length) - 1
    masks = tuple(sum(value << i for i, value in enumerate(row)) for row in supports)

    def rotate(mask, shift):
        return ((mask << shift) & full) | (mask >> (length - shift))

    lag_rows = [
        sum((mask & (rotate(mask, lag) ^ rotate(mask, length - lag))) << (k * length)
            for k, mask in enumerate(masks))
        for lag in range(1, length // 2 + 1)
    ]
    parity_rows = [mask << (k * length) for k, mask in enumerate(masks)]
    pivots = {}
    for row in lag_rows + parity_rows:
        while row:
            column = row.bit_length() - 1
            if column not in pivots:
                pivots[column] = row
                break
            row ^= pivots[column]
    return len(pivots)


def verify_full_source(positive, negative, exact_lags, maximum, squared, modulus, exact_quotient):
    binary = tuple(tuple(a[i % 299] + (-1)**i * b[i % 299] for i in range(598))
                   for a, b in zip(positive, negative, strict=True))
    assert all(set(row) <= {-1, 1} for row in binary)
    assert tuple(map(sum, binary)) == (0, 2, 0, 0)
    corr = periodic(binary)
    assert corr[0] == 2392
    assert all((value + 4) % modulus == 0 for value in corr[1:])
    residuals = [value + 4 for value in corr[1:]]
    assert residuals.count(0) == exact_lags
    assert max(map(abs, residuals)) == maximum
    assert sum(value**2 for value in residuals) == squared
    if exact_quotient:
        compressed = tuple(tuple(sum(row[r::26]) for r in range(26)) for row in binary)
        assert periodic(compressed) == [2304] + [-92] * 25


def verify_fixed_pair_obstruction(positive):
    # A completion makes the combined circulant Gram of the first two
    # words bounded above by 599 times the identity. Probe this directly.
    probe = tuple(1 if min((81 * j) % 299, (-81 * j) % 299) <= 74 else -1
                  for j in range(299))
    probe_corr = periodic((probe,))
    fixed_corr = periodic(positive[:2])
    numerator = sum(a * b for a, b in zip(probe_corr, fixed_corr, strict=True))
    assert probe_corr[0] == 299 and numerator == 263771
    assert numerator > 599 * probe_corr[0]


def verify_reflected_trade(initial, refined):
    assert initial[:2] == refined[:2]
    aligned_pairs = []
    for positive in (initial, refined):
        reflected = tuple(positive[3][(287 - j) % 299] for j in range(299))
        assert all(abs(a) == abs(b) for a, b in zip(positive[2], reflected, strict=True))
        aligned_pairs.append(tuple(tuple((a + sign * b) // 2
                                   for a, b in zip(positive[2], reflected, strict=True))
                                   for sign in (1, -1)))
    before, after = aligned_pairs
    for left, right in zip(before, after, strict=True):
        assert tuple(map(abs, left)) == tuple(map(abs, right))
        assert all(sum(left[r::13]) == sum(right[r::13]) for r in range(13))


def main():
    negative = negative_words()
    positive_supports = tuple(tuple(int(x == 0) for x in a) for a in negative)
    sizes = tuple(map(sum, positive_supports))
    assert sizes == (164, 173, 130, 130) and sum(sizes) == 597
    assert [value % 2 for value in periodic(positive_supports)] == [1] + [0] * 298
    assert support_rank(positive_supports) == 152
    initial = tuple(map(word, POSITIVE_MOD4_C13))
    refined = initial[:2] + tuple(map(word, REFINED_LAST_WORDS))
    mod16 = tuple(map(word, POSITIVE_MOD8))
    verify_positive(initial, negative, 22, 4, exact_quotient=True)
    verify_positive(refined, negative, 45, 4, exact_quotient=True)
    verify_positive(mod16, negative, 30, 8, exact_quotient=False)
    verify_full_source(initial, negative, 89, 80, 414720, 8, exact_quotient=True)
    verify_full_source(refined, negative, 181, 64, 289792, 8, exact_quotient=True)
    verify_full_source(mod16, negative, 121, 112, 833536, 16, exact_quotient=False)
    assert all(initial[2][j] * initial[3][(287 - j) % 299]
               == mod16[2][j] * mod16[3][(287 - j) % 299] for j in range(299))
    verify_reflected_trade(initial, refined)
    verify_fixed_pair_obstruction(refined)
    if "--words" in argv:
        for line in negative:
            print("".join({0:".",1:"+",-1:"-"}[x] for x in line))
    else:
        print("C299 exact negative half, sums (15,6,13,-13); positive support sizes", sizes)
        print("Both positive fixtures have exact C13 and modulo four, with 22 and 45 exact inverse pairs.")
        print("Refined full C598 source: 181 exact nonzero lags, maximum residual 64, squared residual sum 289792.")
        print("Keeping its first two positive words fixed prevents exact completion by a Rayleigh quotient.")
        print("Separate full C598 source: all lags modulo 16 and 121 exact, with the same exact negative half.")


if __name__ == "__main__":
    main()
