"""Exact nested-support width-four witnesses and their quotient residuals."""

from border4_2396 import periodic
from border4_2396_exact_negative import word
from t599_length_change import aperiodic


NEAR_C13 = (
    (
        "...-..-.--+-+--....+++..++-.....+-+-+--....-.+.+.++-...-++++"
        "-..--.+....+++..-+--+++++.-..--....-.+.-.++---+...+.+..-+.-."
        "...--++++-.....-+.-..+-....-+---+.+-..-...-.-..-+.+--+--.-.."
        "++.....-+.-..++---+..+.-+.--..-...+.----++.....-.+..+-.....-"
        "+--++-+...+..+.+-.--..+++-++-..-++.....+.+..+++-+-+.+.-.---"
    ),
    (
        "+..+..-.+--+-++....---.-+++.....---++++....+.-++.-++...-++++"
        "+..++.+..-.+-+..-+--++---.-..++.-..+.+.-.-+-++-...+.+..--.-."
        "...++--+++.....+-.+..--....--+---.+-..+..-+.-..+-.--+--+.-.."
        "++..+..++.-..+---+-..-.--.--..+...-.+-+-++.....+.--.+-.....+"
        "+---+-+...-..-.+-.+-..-+-+--+..--+..+..-.+..---++-+.-.+.+++"
    ),
    (
        "......-+.+-++--++-......-+.......-+.......--.++-+--++-.-...+"
        "-........+-.......-+..-...++...+...-+...+...-+...-...+-...-."
        "..++...-...--........++.......++.......+-.......++.......+-."
        "......++..+...++...+...-+........+-.-----++--.+...-+...-...+"
        "-...+...--..++--++--+.-...--..+--++-+---+--+-+--+-++-++--+-"
    ),
    (
        "..++...-.++++-+++-..--...-...+-...-...-+...+.-----+++-.++..."
        ".....-+...+...--...-..-+.......+-.......-+.......-+.......-+"
        ".......+-........-+...-...-+...-...+-...+...+-...+...+-...+."
        "..-+...+..++.......--........--...+.+--+-+--+.++.......+-..."
        "....++......-+---+---.++......+++--+-++--+------+-++++--+-+"
    ),
)

MORE_EXACT_LAGS = (
    (
        "...+..+.+-+++-+....-+-..---.....+---+++....+.-.-.--+...++--+"
        "-..++.+....-+-..+-++-+---.+..-+....+.-.+.+-++++...-.+..--.-."
        "...++-----.....--.-..-+....-++---.-+..-...+.+..+-.++--+-.+.."
        "-+.....--.+..-++--+..-.++.+-..-...-.-+++--.....-.-..-+.....-"
        "+--+++-...-..+.--.++..-+-++++..+-+.....-.-..-+--+++.-.+.+++"
    ),
    (
        "+..-..+.-----+-....+-+.---+.....--+++--....-.++-.+--...++--+"
        "+..--.+..-.---..+-++-++++.+..+-.-..-.-.+.--+---...-.+..-+.-."
        "...--++--+.....++.+..++....-----+.-+..+..--.+..-+.-+++++.+.."
        "-+..+..+-.+..--+-+-..+.+-.+-..+...+.++-+--.....+.+-.-+.....+"
        "+---++-...+..-.--.-+..+++----..+++..+..+.-..+-+++++.+.-.---"
    ),
    (
        "......-+.+----++-+......+-.......+-.......--.++-+++++-.-...+"
        "-........++.......--..-...+-...-...++...-...-+...+...--...+."
        "..+-...+...-+........++.......--.......+-.......-+.......++."
        "......++..+...+-...-...+-........--.+-++-++--.+...++...+...+"
        "+...+...+-..-+-----+-.+...--..+-+----++----++++--+---+-+-+-"
    ),
    (
        "..++...+.--+-+++++..-+...-...--...+...--...+.-------++.+-..."
        ".....+-...-...+-...-..-+.......--.......--.......-+.......+-"
        ".......+-........++...+...++...+...++...-...+-...-...++...-."
        "..++...+..-+.......+-........--...+.+---++--+.++.......-+..."
        "....--......+--+--+--.++......++++++---++++-+--------+++--+"
    ),
)


def nested_negative_words():
    cw = word("--++-+.+.++..")
    u, v = map(word, ("+--.+++++......+++--.+-", ".+-.++-++......--+-+.-+"))
    assert periodic((cw,)) == [9] + [0] * 12
    assert periodic((u, v)) == [29] + [0] * 22
    for j in range(23):
        assert abs(u[j]) - abs(v[j]) == (j == 0)
        assert abs(u[j]) == abs(u[-j]) and abs(v[j]) == abs(v[-j])
    first = tuple(tuple(cw[i % 13] * row[i % 23] for i in range(299)) for row in (u, v))

    a, b, c, d = map(word, ("+.-+-..++......", "......+..---+--", "+---+-..-", "+-..---.+"))
    assert aperiodic((a, b)) == [13] + [0] * 14
    assert aperiodic((c, d)) == [13] + [0] * 8
    assert all(not (x and y) for x, y in zip(a, b, strict=True))
    e = tuple(x * u + y * v for x, y in zip(a, b, strict=True)
              for u, v in zip(c, reversed(d), strict=True))
    f = tuple(x * u - y * v for x, y in zip(a, b, strict=True)
              for u, v in zip(d, reversed(c), strict=True))
    assert aperiodic((e, f)) == [169] + [0] * 134
    third = e + f[::-1]
    fourth = f + tuple(-x for x in reversed(e))
    assert aperiodic((third, fourth)) == [338] + [0] * 269
    second = tuple(row + (0,) * 29 for row in (third, fourth))
    result = first + second
    assert tuple(map(sum, result)) == (15, 6, -13, -13)
    assert periodic(result) == [599] + [0] * 298
    return result


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            column = row.bit_length() - 1
            if column not in pivots:
                pivots[column] = row
                break
            row ^= pivots[column]
    return len(pivots)


def verify_switch_dimensions(positive):
    common = {i for i, value in enumerate(positive[0]) if value}
    extra = {i for i, value in enumerate(positive[1]) if value} - common
    assert len(common) == 164 and len(extra) == 9
    assert all(positive[1][i] for i in common)
    assert all(i % 23 == 0 for i in extra)
    for lag in range(1, 150):
        # An odd edge touches one extra site and one common site. In a
        # cyclic lag all its switches belong to a single residue pair.
        sites = {i for i in common if ((i - lag) % 299 in extra) ^ ((i + lag) % 299 in extra)}
        assert all(min(i % 23, (-i) % 23) == min(lag % 23, (-lag) % 23) for i in sites)
    dimensions = []
    for residue in range(12):
        sites = sorted(i for i in common if min(i % 23, (-i) % 23) == residue)
        rows = [sum((((i - lag) % 299 in extra) ^ ((i + lag) % 299 in extra)) << k
                    for k, i in enumerate(sites)) for lag in range(1, 150)]
        dimensions.append(len(sites) - rank(rows))
    assert dimensions == [1, 1, 1, 13, 1, 1, 1, 1, 1, 13, 13, 13]

    reflected = tuple(positive[3][(269 - i) % 299] for i in range(299))
    assert tuple(map(abs, reflected)) == tuple(map(abs, positive[2]))
    partition = [
        {i for i, value in enumerate(positive[2]) if value and (value == reflected[i]) == agree}
        for agree in (True, False)
    ]
    columns = [
        sum((((i - lag) % 299 in sites) ^ ((i + lag) % 299 in sites)) << (lag - 1)
            for lag in range(1, 150)) | (1 << (149 + group))
        for group, sites in enumerate(partition) for i in sites
    ]
    assert len(columns) == 130 and rank(columns) == 128


def verify_source(negative, patterns, quotient_half, exact_lags, maximum, energy):
    positive = tuple(map(word, patterns))
    assert tuple(map(sum, positive)) == (0, 1, 0, 0)
    assert tuple(sum(abs(x) for x in row) for row in positive) == (164, 173, 130, 130)
    assert all(u * u + v * v == 1 for a, b in zip(positive, negative, strict=True)
               for u, v in zip(a, b, strict=True))
    verify_switch_dimensions(positive)
    pos_corr = periodic(positive)
    assert pos_corr[0] == 597 and all((value + 2) % 8 == 0 for value in pos_corr[1:])

    compressed = tuple(tuple(sum(row[r::13]) for r in range(13)) for row in positive)
    actual = periodic(compressed)
    quotient = [a - b for a, b in zip(actual, [553] + [-46] * 12, strict=True)]
    assert quotient == quotient_half + quotient_half[1:][::-1]

    binary = tuple(tuple(a[i % 299] + (-1)**i * b[i % 299] for i in range(598))
                   for a, b in zip(positive, negative, strict=True))
    assert all(set(row) <= {-1, 1} for row in binary)
    assert tuple(map(sum, binary)) == (0, 2, 0, 0)
    r = periodic(binary)
    assert r[0] == 2392
    errors = [value + 4 for value in r[1:]]
    assert all(value % 16 == 0 for value in errors)
    assert errors.count(0) == exact_lags and max(map(abs, errors)) == maximum
    assert sum(value**2 for value in errors) == energy
    return sum(value**2 for value in quotient)


if __name__ == "__main__":
    t = nested_negative_words()
    near = verify_source(t, NEAR_C13, [0, 0, 0, -8, 8, 0, 0], 85, 80, 610304)
    broad = verify_source(t, MORE_EXACT_LAGS, [0, 8, 16, 16, -16, 8, -32], 129, 96, 606208)
    assert near == 256 and broad == 3840
    print("Nested exact T and two full modulo-sixteen S lifts verified.")
    print("Nearest C13 witness: two opposite ±8 inverse pairs; more exact full lags: 129.")
