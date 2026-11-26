"""Replay the -8/+8 C13 transfer at ±2/±3 and two of its lifts."""

from border4_2396 import periodic
from border4_2396_exact_negative import word
from border4_2396_nested import nested_negative_words
from border4_2396_two_fibers import SOURCE as TWO_FIBERS

N = 299
Q = 13
NEAR = (0, 0, 8, -8, 0, 0, 0, 0, 0, 0, -8, 8, 0)
C13_TARGET = (553,) + (-46,) * (Q - 1)

FULL_MOD16 = (
    (
        "...+..+.--+--++....---..++-.....+-+-+-+....+.+.-.---...++-+-"
        "-..-+.+....++-..-+-+-+++-.+..+-....+.+.-.+-+-+-...-.-..++.-"
        "....+-+---+.....++.+..++....-+-+--.++..-...+.+..-+.-+-+-+.-"
        "..++.....++.+..---+++..+.--.+-..+...+.--+--+.....-.-..-"
        "+.....-+--+-++...+..+.--.++..+--+---..--+.....-.+..-----+-"
        ".+.+.---"
    ),
    (
        "+..+..+.++-+++-....-++.++++.....--+-++-....-.+--.+--"
        "...++++++..-+.-..+.++-..++-++--++.+..--.+..+.-.-.-++-+-...-"
        ".-..-+.+....-++-+-+.....++.-..++....+-+--+.--..-..-+.-..-+.-"
        "-+-++.+..++..-..--.-..-+---+..+.--.+-..-...-.-++---.....-.--"
        ".++.....----++--...+..+.+-.+-..-+-++-+..-++..-..+.-..+-++---"
        ".-.+.---"
    ),
    (
        "......+-.------+--......+-.......--.......+-.+++-++-+-"
        ".+...+-........-+.......--..-...-+...-...++...+...++...+...-"
        "+...-...-+...+...--........++.......++.......+-"
        ".......++.......+-.......--..-...--...+...+-........++.+-+-"
        "++---.-...-+...-...+-...+...++..+-+-+-+-+.-...++..----++----"
        "-++-++-++++-+--+++-"
    ),
    (
        "..--...+.-+-+++-+-..--...-...--...+...-+...+.+++-++-+-.--"
        "........+-...-...++...-..++.......++.......--.......+-"
        ".......--.......--........++...-...--...+...-+...+...--...-"
        "...--...+...-+...+..-+.......-+........++...-.+-+--+---.--"
        ".......++.......+-......++-++-+++.+-......+---++-+---++--+--"
        "+++++--++++"
    ),
)

C13_LIFT_SOURCE = (
    (
        "...-..+.+--++-+....+--..+++.....-+--++-....-.+.-.-++...+++-"
        "++..++.+....+++..-+-+--+--.-..+-....+.-.+.++++++...+.-..-+.-"
        "....--+++++.....-+.-..-+....-+--++.++..+...+.-..--.+---+-.-"
        "..++.....-+.-..-+-+--..+.--.-+..-...-.-----+.....-.-..--"
        ".....--++-++-...+..+.+-.--..++++-+-..++-.....-.-..---++-"
        "+.+.-.---"
    ),
    (
        "-..-..+.--+++--....+++.+++-.....+++++++....+.+-"
        "+.+++...++++++..-+.+..-.-+-..++-++-+--.+..++.-..+.+.+.-++--"
        "+...+.+..++.-....+++-+++.....-+.+..++....---+++.+-..+..--"
        ".+..-+.+-+--+.+..-+..-..++.-..-+--++..-.++.-+..-...-.------"
        ".....-.--.--.....+---+---...-..-.-+.--..---+---..--+..+..-.-"
        "..--+----.-.-.---"
    ),
    (
        "......--.+--+----+......--.......++.......-+.-++--++--.-...-"
        "+........--.......+-..+...++...+...++...-...++...+...--"
        "...+...+-...+...-+........-+.......--.......++.......-"
        "+.......+-.......-+..-...+-...+...+-........-+.--+++-+-+.-"
        "...--...+...+-...+...+-..+-------+.-...++..+++++-+-+-++++-+-"
        "+---+----+++"
    ),
    (
        "..--...+.-++++++--..+-...-...+-...-...++...+.-+-++--++.-"
        "+........+-...-...--...+..-+.......+-.......-+.......-"
        "+.......++.......--........++...-...++...-...-+...-...+-"
        "...+...--...-...--...-..+-.......+-........++...+.+---++--"
        "+.--.......-+.......++......-+-++-++-.++......---++++-+++-+-"
        "+----+++-+-----"
    ),
)



def compressed(row, center=0):
    return tuple(sum(row[(i + center) % Q::Q]) for i in range(Q))


def quotient_residual(rows):
    return tuple(a - b for a, b in zip(periodic(tuple(map(compressed, rows))), C13_TARGET, strict=True))


def raw_norms(positive, negative):
    assert all(u * u + v * v == 1 for a, b in zip(positive, negative, strict=True)
               for u, v in zip(a, b, strict=True))
    assert tuple(map(sum, positive)) == (0, 1, 0, 0)
    norms = periodic(positive)
    assert norms[0] == 597
    assert all((a + 2) % 4 == 0 for a in norms[1:])
    binary = tuple(tuple(a[i % N] + (-1)**i * b[i % N] for i in range(2 * N))
                   for a, b in zip(positive, negative, strict=True))
    assert all(set(row) <= {-1, 1} for row in binary)
    source = periodic(binary)
    assert source[0] == 8 * N
    return norms, source[1:]


def reflect(row):
    return tuple(row[(269 - i) % N] for i in range(N))


def transfer(patterns, axis, changed, factors):
    s = tuple(map(word, patterns))
    x = tuple((a + b) // 2 for a, b in zip(s[2], reflect(s[3]), strict=True))
    assert all(x[(axis - j) % N] == -a for j, a in enumerate(x))
    assert all(x[i] and (axis - i) % N in changed for i in changed)
    u = tuple(0 if i in changed else a for i, a in enumerate(x))
    v = tuple(a if i in changed else 0 for i, a in enumerate(x))
    center = 7 * axis % Q
    assert tuple(compressed(a, center)[1:7] for a in (u, v)) == factors
    a, b = s[2], reflect(s[3])
    t = s[:2] + (tuple(-a[i] if i in changed else a[i] for i in range(N)),
                reflect(tuple(-b[i] if i in changed else b[i] for i in range(N))))
    expected = tuple(8 * sum(u[j] * v[(i + axis - j) % N] for j in range(N))
                     for i in range(N))
    assert tuple(b - a for a, b in zip(periodic(s), periodic(t), strict=True)) == expected
    assert tuple(b - a for a, b in zip(quotient_residual(s), quotient_residual(t), strict=True)) == (
        tuple(-a for a in NEAR)
    )
    return s, t, expected


def verify():
    negative = nested_negative_words()
    before, after, difference = transfer(
        FULL_MOD16, 0, {59, 240},
        ((0, 0, 0, -1, 0, 0), (0, 0, 0, 0, 0, -1)),
    )
    for rows in (before, after):
        _, binary = raw_norms(rows, negative)
        assert all((a + 4) % 16 == 0 for a in binary)
    assert sum(a != 0 for a in difference) <= 20

    before, after, difference = transfer(
        C13_LIFT_SOURCE, 174, {15, 159, 33, 141, 52, 122, 69, 105},
        ((-1, 0, 1, -1, 0, 1), (0, -1, 0, -1, 1, -1)),
    )
    assert sum(a != 0 for a in difference) <= 64
    near = tuple(map(word, TWO_FIBERS))
    assert tuple(map(compressed, before[:2])) == tuple(map(compressed, near[:2]))
    assert quotient_residual(before) == NEAR and quotient_residual(after) == (0,) * Q
    for rows in (before, after):
        raw, binary = raw_norms(rows, negative)
        assert sum((a + 2) % 8 == 0 for a in raw[1:]) == 162
        assert sum((a + 4) % 16 == 0 for a in binary) == 325
    print("Verified exact ±2/±3 transfer over the integer group ring with full modulo sixteen.")
    print("Multi-pair source lifts the two original first C13 margins and gives exact C13 at raw mod4.")


if __name__ == "__main__":
    verify()
