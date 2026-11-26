"""Replay a C13 residual transfer preserving the full modulo-sixteen source."""

from border4_2396 import periodic
from border4_2396_exact_negative import word
from border4_2396_nested import nested_negative_words

N = 299
ALIGNMENT = 269
AXIS = 246
PAIRS = ((15, 231), (69, 177), (254, 291), (256, 289))
INITIAL_SIGNS = (-1, -1, 1, -1)

SOURCE = (
    (
        "...-..-.-+--+-+....+-+..+-+.....+++-+++....+.+.+.++-...++-"
        "+++..--.-....+--..-+----+--.+..-+....-.+.-.+++-+-...-.+..-"
        "+.+....++-++++.....+-.+..+-....+----+.+-..-...-.-..-+.----+-"
        ".+..--.....+-.-..--++-+..-.+-.++..+...+.-+++++.....-.-..--"
        ".....----+-++...+..-.++.+-..+-++---..+-+.....-.+..+------"
        ".+.+.-+-"
    ),
    (
        "+..-..-.--+-+++....+++.+--+.....----+--....-.+--.---"
        "...++++++..+-.+..-.+++..-++---+-+.-..+-.-..+.-.-.+-----"
        "...+.-..-+.+....++--+++.....++.-..+-....++-+++.++..-..--"
        ".+..++.-++++-.+..--..+..+-.-..-++-++..-.-+.+-..-...+.++++--"
        ".....+.-+.-+.....--++-+-+...-..-.--.-+..--++--+..+--..+..+.-"
        "..--++---.-.+.-+-"
    ),
    (
        "......-+.--++++-+-......--.......++.......+-.-+---+-++.+...-"
        "-........-+.......-+..-...-+...+...++...+...++...+...+-...-"
        "...++...+...++........++.......++.......++.......++.......+-"
        ".......-+..-...+-...-...--........--.+-+-++-++.-...-"
        "+...+...-+...+...-+..--++--++-.-...--..---++---+----+-+---"
        "++-+--+---"
    ),
    (
        "..++...+.+--+--+++..-+...-...-+...-...++...+.--+--+-+-"
        ".++........++...+...+-...+..-+.......++.......--.......--"
        ".......--.......--........--...-...--...+...+-...-...--...-"
        "...--...-...-+...+..-+.......--........++...-.--+-+++-+.+-"
        ".......--.......++......+------++.-+......+++-++---++++-+-"
        "++++-+++--+++"
    ),
)


def reflect(row):
    return tuple(row[(ALIGNMENT - i) % N] for i in range(N))


def quotient_residual(positive, negative):
    assert tuple(map(sum, positive)) == (0, 1, 0, 0)
    assert all(a * a + b * b == 1 for u, v in zip(positive, negative, strict=True)
               for a, b in zip(u, v, strict=True))
    positive_corr = periodic(positive)
    assert positive_corr[0] == 597
    assert all((value + 2) % 8 == 0 for value in positive_corr[1:])

    binary = tuple(tuple(a[i % N] + (-1)**i * b[i % N] for i in range(2 * N))
                   for a, b in zip(positive, negative, strict=True))
    assert all(set(row) <= {-1, 1} for row in binary)
    binary_corr = periodic(binary)
    assert binary_corr[0] == 8 * N
    assert all((value + 4) % 16 == 0 for value in binary_corr[1:])

    quotient = tuple(tuple(sum(row[i::13]) for i in range(13)) for row in positive)
    return tuple(value - (553 if d == 0 else -46)
                 for d, value in enumerate(periodic(quotient)))


def main():
    negative = nested_negative_words()
    positive = tuple(map(word, SOURCE))
    aligned = reflect(positive[3])
    assert tuple(map(abs, positive[2])) == tuple(map(abs, aligned))
    x = tuple((a + b) // 2 for a, b in zip(positive[2], aligned, strict=True))
    y = tuple((a - b) // 2 for a, b in zip(positive[2], aligned, strict=True))
    assert not any(a and b for a, b in zip(x, y, strict=True))
    assert {i for i, value in enumerate(x) if value} == {i for pair in PAIRS for i in pair}
    assert tuple(x[i] for i, _ in PAIRS) in (INITIAL_SIGNS, tuple(-a for a in INITIAL_SIGNS))
    assert all((i + j) % N == AXIS and x[i] == -x[j] for i, j in PAIRS)

    changed = set(PAIRS[1] + PAIRS[3])
    flipped = tuple(-a if i in changed else a for i, a in enumerate(x))
    assert sum(x) == sum(flipped) == 0
    assert all((a - b) % 4 == 0 for a, b in zip(periodic((x,)), periodic((flipped,)), strict=True))
    after = positive[:2] + (
        tuple(a + b for a, b in zip(flipped, y, strict=True)),
        reflect(tuple(a - b for a, b in zip(flipped, y, strict=True))),
    )

    before_residual = quotient_residual(positive, negative)
    after_residual = quotient_residual(after, negative)
    assert before_residual == (-160, 64, 80, 32, 16, -80, -32, -32, -80, 16, 32, 80, 64)
    assert tuple(b - a for a, b in zip(before_residual, after_residual, strict=True)) == (
        0, 0, 0, 8, -8, 0, 0, 0, 0, -8, 8, 0, 0,
    )
    print("Exact T and both full modulo-sixteen sources verified.")
    print("C13 transfer: +8 at lags ±3 and -8 at lags ±4.")


if __name__ == "__main__":
    main()
