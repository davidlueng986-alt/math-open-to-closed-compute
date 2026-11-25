"""Replay the two-fiber phase source with minimum nonzero C13 residual."""

from border4_2396 import periodic
from border4_2396_exact_negative import word
from border4_2396_nested import NEAR_C13, nested_negative_words, verify_source

N = 299
FIBERS = {8, 12}

SOURCE = (
    (
        "...-..+.----+++....+--..--+.....-+-++--....+.-.-.-++...-"
        "+++++..++.+....-++..-+-+-+-++.+..-+....-.-.-.++-++-...-.+..-"
        "-.+....--+-+++.....+-.-..--....++++--.++..-...+.-..++.+-++--"
        ".-..+-.....-+.+..-+--+-..-.--.+-..+...+.+-+-+-.....+.-..--"
        ".....-------+...+..+.-+.++..+-+--+-..++-.....-.-..+--++--"
        ".+.+.-++"
    ),
    (
        "+..+..+.--+++--....-+-.--+-.....++--++-....-.+++.+++...-"
        "+++++..-+.+..-.---..---+-++--.-..++.-..+.-.+.-++--+...-.-..-"
        "-.+....+++++++.....-+.-..++....+--+++.+-..+..--.+..-+.-----"
        "+.+..++..+..++.-..-+---+..+.++.++..-...-.+-----.....-.--.-"
        "+.....+--++---...-..-.++.--..---++--..++-..+..+.+..--+-+--.-"
        ".+.+-+"
    ),
    (
        "......--.++++++--+......++.......++.......--.-+---+-+-"
        ".+...+-........++.......+-..+...--...+...-+...-...++...+...-"
        "-...-...--...-...--........-+.......++.......+-.......+-"
        ".......--.......+-..+...--...-...+-........--.-+-+-+--+.-"
        "...+-...-...++...+...--..+-+-+++--.-...--..++++--++-+--"
        "++++++-+-++++--+-"
    ),
    (
        "..++...-.-+-+-+---..--...-...--...-...+-...-.+-+---+--.+-"
        "........+-...-...++...-..++.......++.......++.......-"
        "+.......-+.......++........-+...-...+-...-...++...-...++...-"
        "...+-...+...+-...-..--.......+-........--...-.+-+------"
        ".++.......++.......+-......+-++++-+-.-+......+++--+++-++-+-"
        "+-+--++-+++--++"
    ),
)


def verify():
    base = tuple(map(word, NEAR_C13))
    result = tuple(map(word, SOURCE))
    support_margins = [sum(map(abs, base[1][j::13])) for j in range(13)]
    assert all(size % 2 for size in support_margins)
    assert {j for j, size in enumerate(support_margins) if size == 23} == {6, 8, 11, 12}
    rotated = base[:1] + (
        tuple(-value if i % 13 in FIBERS else value for i, value in enumerate(base[1])),
    ) + base[2:]
    assert all((a - b) % 4 == 0 for a, b in zip(periodic(base), periodic(rotated), strict=True))
    for i in range(N):
        # After the two-fiber switch, the first two rows are switched
        # together on their common support.
        first_flip = result[0][i] != rotated[0][i]
        assert not first_flip or rotated[0][i]
        assert result[0][i] == (-rotated[0][i] if first_flip else rotated[0][i])
        assert result[1][i] == (-rotated[1][i] if first_flip else rotated[1][i])
        j = (269 - i) % N
        assert (result[2][i] != rotated[2][i]) == (result[3][j] != rotated[3][j])

    quotient = verify_source(nested_negative_words(), SOURCE, [0, 0, 8, -8, 0, 0, 0],
                             141, 80, 659456)
    assert quotient == 256
    print("Two-fiber exact T and full modulo-sixteen lift verified.")
    print("C13 residual +8 at ±2 and -8 at ±3; 141 exact original lags.")


if __name__ == "__main__":
    verify()
