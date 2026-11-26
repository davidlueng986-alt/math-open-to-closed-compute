"""Replay three exact C13 sources, a fixed-first exclusion, and the full-y kernel."""

from collections import defaultdict
from itertools import combinations

from border4_2396 import periodic
from border4_2396_exact_negative import word
from border4_2396_fixed_first import incident, reflect, TARGET
from border4_2396_nested import nested_negative_words
from border4_2396_shifted_tail import compress, verify_lift
from border4_2396_two_fibers import SOURCE as TWO_FIBER_SOURCE

N = 299
H = N // 2
Q = 13

SOURCE = (
    (
        "...-..-.----+++....---..--+.....-+-++--....+.+.-.-++...-++-"
        "++..++.+....+++..-++-++-+-.+..-+....-.-.-.++-++-...+.+..--"
        ".+....+-+-+++.....+-.-..--....++++--.++..-...+.-..+-.+-++--"
        ".-..+-.....--.+..-+--+-..+.--.+-..+...+.+-+-+-.....-.-..--"
        ".....-------+...+..+.-+.++..+-+-++-..++-.....-.-..+--++-+.-"
        ".+.-++"
    ),
    (
        "+..+..+.--+++--....-+-.--+-.....-+--++-....-.-++.+++...-++-"
        "++..-+.+..-.+--..-----++-+.-..++.-..+.-.+.-++--+...-.-..--"
        ".+....+++++++.....-+.-..++....--++++.+-..+..-+.+..-+.------"
        ".+..++..+..+-.-..-++--+..-.++.++..-...+.+-----.....-.--.-"
        "+.....+--++---...-..+.++.--..+--++--..++-..+..-.+..-++-+--.-"
        ".+.+-+"
    ),
    (
        "......-+.-++++--++......+-.......+-.......++.-+---+---"
        ".+...++........-+.......++..+...+-...+...+-...-...--...-"
        "...+-...-...-+...+...++........++.......--.......+-.......-"
        "+.......+-.......-+..-...++...+...--........-+.---+----+.-"
        "...+-...+...+-...-...--..+---+-+-+.-...-+..--++---++---"
        "+++++----++++++++"
    ),
    (
        "..++...-.-+-----+-..-+...+...+-...-...-+...-.---+-++-+.--"
        "........++...-...--...+..-+.......--.......++.......-"
        "+.......--.......++........++...-...-+...+...+-...+...++...-"
        "...++...-...++...-..-+.......+-........-+...+.+-+--+--+.+-"
        ".......-+.......--......-+--++++-.-+......+-++-++-+++--+----"
        "--+-+-+++++"
    ),
)


MORE_MOD16 = (
    (
        "...-..-.---++++....---..+++.....-+-++-+....+.+.+.-+-...-"
        "+++++..-+.+....-+-..-++-++-++.+..++....-.-.-.+++++-...-"
        ".+..+-.+....----+-+.....+-.-..++....++-+--.++..-...+.-..+-"
        ".+-++-+.-..++.....-+.+..-+--+-..-.--.--..+...+.--+---.....-"
        ".-..--.....-+-+--+-...+..-.++.--..+-+-+++..+--.....+.-..-+-"
        "++-+.-.-.---"
    ),
    (
        "+..+..-.+-+-+--....-+-.-+--.....+++-+++....-.-++.+-+...-"
        "+++++..-+.+..-.+-+..-+---++-+.-..++.-..+.+.-.-----+...-"
        ".+..++.+....++-++--.....--.-..+-....---+-+.+-..+..--.-..++.-"
        "----+.-..++..+..++.+..-++--+..-.++.-+..-...-.+---+-.....-.--"
        ".+-.....+--++-++...-..-.++.++..+--++--..-+-..+..-.+..-++-+--"
        ".+.+.+--"
    ),
    (
        "......-+.-++++--++......+-.......--.......+-.++---+-+-.+...-"
        "+........+-.......--..-...-+...+...++...-...--...+...+-"
        "...+...+-...+...--........++.......+-.......+-.......-"
        "+.......++.......+-..-...+-...-...--........+-.+--+++---.-"
        "...+-...+...-+...-...--..------+-+.+...-+..-+++---++++++++-"
        "++-+++-+--+-+"
    ),
    (
        "..++...+.-+--+--++..-+...+...-+...-...-+...-.+---+++--"
        ".++........++...+...+-...+..+-.......+-.......++.......-"
        "+.......-+.......++........--...-...+-...-...+-...-...++...-"
        "...-+...-...--...+..+-.......-+........--...+.+++--+---.--"
        ".......--.......--......-+--++++-.-+......+++-++----++-----"
        "++++-+-+++-+"
    ),
)


MORE_EXACT = (
    (
        "...-..+.+--++++....---..--+.....-+-+++-....+.+.-.-++...-++-"
        "+-..++.+....++-..-++-++-+-.-..-+....-.+.-.+++++-...-.-"
        "..++.+....+-+-+-+.....+-.-..++....++-++-.+-..-...-.-..-+.+-"
        "++-+.-..--.....--.+..----+-..-.+-.--..+...-.--+-+-"
        ".....+.+..+-.....-+----++...+..-.++.-+..+-+-++-..+--.....-"
        ".+..+--++-+.+.-.---"
    ),
    (
        "+..+..+.+-+-+--....-++.--+-.....-++-+--....-.+++.+++...-++-"
        "+-..+-.+..-.+--..-+---++--.-..--.-..+.+.-.-++--+...-.-..+-"
        ".+....-++++++.....--.-..++....---+++.--..+..-+.+..--.-----"
        "+.-..--..+..+-.-..-++--+..-.++.-+..-...+.+---+-.....-.--"
        ".++.....+--++-++...-..+.++.-+..+--++-+..++-..+..-.+..+++-+--"
        ".+.-.+++"
    ),
    (
        "......-+.-++++-+++......+-.......--.......-+.-+-+--+--"
        ".+...+-........--.......+-..-...--...+...--...-...--...+...-"
        "-...+...--...-...+-........+-.......+-.......++.......-"
        "+.......--.......++..+...-+...+...+-........+-.+-+++---"
        "+.+...+-...-...-+...-...+-..+++++-+-+.-...--..++++-----++-+-"
        "+++--+++---++++"
    ),
    (
        "..-+...-.-+---++--..--...+...-+...+...-+...+.---+++---"
        ".++........+-...-...-+...-..--.......-"
        "+.......++.......++.......-+.......-+........-+...+...++...-"
        "...++...-...++...-...+-...-...+-...+..++.......--"
        "........++...+.+--+----+.++.......--.......--......-++-++++-"
        ".-+......+-+++-----+--+-+--++-++-+++--"
    ),
)


def reducer(generators):
    pivots = {}
    for position, column in generators:
        witness = 1 << position
        while column:
            key = column.bit_length() - 1
            if key not in pivots:
                pivots[key] = column, witness
                break
            value, preimage = pivots[key]
            column ^= value
            witness ^= preimage
    order = sorted(pivots.items(), reverse=True)

    def reduce(column):
        witness = 0
        for key, (value, mask) in order:
            if column >> key & 1:
                column ^= value
                witness ^= mask
        return column, witness

    return len(pivots), reduce


def support(row):
    return {i for i, a in enumerate(row) if a}


def phase_errors():
    groups = [[] for _ in range(7)]
    for d in range(1, H + 1):
        residue = d % Q
        groups[min(residue, Q - residue)].append(1 << (d - 1))
    return [0] + [a | b for group in groups for a, b in combinations(group, 2)]


def all_small_errors(reduce, target):
    generators = phase_errors()
    assert len(generators) == 1574
    table = defaultdict(list)
    pairs = tuple((error, reduce(error)[0]) for error in generators)
    for i, (a, x) in enumerate(pairs):
        for b, y in pairs[i:]:
            table[x ^ y].append(a ^ b)

    assert sum(map(len, table.values())) == 1239525
    assert target
    matches = 0
    masks = set()
    for key, a in table.items():
        complement = key ^ target
        if complement < key:
            continue
        b = table.get(complement)
        if b:
            matches += len(a) * len(b)
            masks.update(x ^ y for x in a for y in b)
    assert matches == 181065 and len(masks) == 28542
    return masks


def verify_radius(positive):
    a, b = positive[2], reflect(positive[3])
    shared = support(a)
    assert shared == support(b) and len(shared) == 130
    relative_columns = [(i, incident(shared, i)) for i in shared]
    relative_rank, _ = reducer(relative_columns)
    assert relative_rank == 129

    x = tuple((u + v) // 2 for u, v in zip(a, b, strict=True))
    y = tuple((u - v) // 2 for u, v in zip(a, b, strict=True))
    assert sum(x) == sum(y) == 0
    places = tuple(map(support, (x, y)))
    assert all(places) and places[0].isdisjoint(places[1]) and places[0] | places[1] == shared
    generators = [(i, incident(p, i) | (1 << (H + g)))
                  for g, p in enumerate(places) for i in p]
    rank, reduce = reducer(generators)
    assert rank == 128

    initial = sum(((((value + 2) // 4) % 2) << i)
                  for i, value in enumerate(periodic(positive)[1:H+1]))
    assert initial.bit_count() == 26
    target, _ = reduce(initial)
    assert target

    first = periodic(tuple(map(compress, positive[:2])))
    last_goal = tuple((a - b) // 2 for a, b in zip(TARGET, first, strict=True))
    assert all((a - b) % 2 == 0 for a, b in zip(TARGET, first, strict=True))
    balanced = exact = 0
    for error in all_small_errors(reduce, target):
        assert error.bit_count() in (6, 8)
        rest, flip = reduce(initial ^ error)
        assert not rest
        u, v = (tuple(-a if flip >> i & 1 else a for i, a in enumerate(row)) for row in (x, y))
        if sum(u) or sum(v):
            continue
        balanced += 1
        exact += periodic(tuple(map(compress, (u, v)))) == list(last_goal)
    assert balanced == 1129 and exact == 0
    print("Fixed first words: no full mod16; exact C13 has at least ten inverse misses.")



def product_mod2(a, b, size):
    result = 0
    mask = (1 << size) - 1
    for i in range(size):
        if b >> i & 1:
            result ^= ((a << i) | (a >> (size - i))) & mask
    return result


def reverse_mod2(word, size):
    return sum(1 << ((-i) % size) for i in range(size) if word >> i & 1)


def verify_full_y(negative):
    x_full = {6, 8, 11, 12}
    r = sum(1 << i for i in range(Q) if i not in x_full)
    short = tuple(sum((sign != ".") << i for i, sign in enumerate(pattern)) for pattern in
                  ("+--.+++++......+++--.+-", ".+-.++-++......--+-+.-+"))
    u, v = short
    assert u ^ v == 1 and all(w == reverse_mod2(w, 23) for w in short)
    assert product_mod2(r, reverse_mod2(r, Q), Q) == 1
    full = [i for i in range(23) if not (u >> i & 1)]
    assert full == [3, 9, 10, 11, 12, 13, 14, 20]
    assert all(abs(a) == ((r >> (i % Q)) & (w >> (i % 23)) & 1)
               for row, w in zip(negative[:2], short, strict=True) for i, a in enumerate(row))

    even_columns = [(1 << full[0]) ^ (1 << j) for j in full[1:]]
    columns = [product_mod2(w, c, 23) for w in short for c in even_columns]
    rank, _ = reducer(enumerate(columns))
    assert rank == 14

    r_squared = product_mod2(r, r, Q)
    involution = [product_mod2(r_squared, reverse_mod2(1 << j, Q), Q) for j in range(Q)]
    rank, _ = reducer((j, a ^ (1 << j)) for j, a in enumerate(involution))
    assert rank == 6
    print("Full-y mod-four frame: two independent row kernels of dimension 46.")


def main():
    negative = nested_negative_words()
    positive = verify_lift(SOURCE, negative, [0] * 7, 493, 93, 112, 698880)
    near = tuple(map(word, TWO_FIBER_SOURCE))
    assert tuple(sum(a != b for a, b in zip(u, v, strict=True))
                 for u, v in zip(positive, near, strict=True)) == (18, 18, 56, 56)
    broader = verify_lift(MORE_MOD16, negative, [0] * 7, 501, 101, 80, 551936)
    assert tuple(map(compress, broader)) == tuple(map(compress, positive))
    assert tuple(sum(a != b for a, b in zip(u, v, strict=True))
                 for u, v in zip(positive, broader, strict=True)) == (44, 46, 48, 48)
    more_exact = verify_lift(MORE_EXACT, negative, [0] * 7, 501, 125, 88, 580608)
    assert tuple(map(compress, more_exact)) == tuple(map(compress, positive))
    assert tuple(sum(a != b for a, b in zip(u, v, strict=True))
                 for u, v in zip(broader, more_exact, strict=True)) == (44, 46, 52, 52)
    print("Exact C13 and exact T: 493/93, 501/101 and 501/125 mod16/fully exact.")
    verify_radius(positive)
    verify_full_y(negative)


if __name__ == "__main__":
    main()
