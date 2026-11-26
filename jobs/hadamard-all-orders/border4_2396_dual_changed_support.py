"""Replay exact dual quotient and raw-mod8 witnesses on altered supports."""

from border4_2396 import periodic
from border4_2396_dual_mod5_forest import FACTORS_5, check_factors, forest
from border4_2396_dual_quotient import replay
from border4_2396_primitive_field import remainder
from border4_2396_exact_negative import word
from border4_2396_nested import nested_negative_words

N = 299
REFLECTION_MULTIPLIER = 116
REFLECTED_HEAD_MASKS = (
    0x104A04C0E80440A92088902140C21A1EC0201A1208B544123010201410814A253388410522A,
    0xB009008406101821CC20680680901441A21F8220BE44124450229804C0FA019318C94C8A0,
    0x7B311A3045B41018805DC0000884802010000C020000C40031088C40000083A0C02000188C0,
    0x48514FD8055D0001004D0400180004460101800460180802000080C88060017C8040003160C,
)
CYCLIC_TAIL_MASKS = (
    0x300A20209C1204E83283A0052084022A1104168240130194320864A73011C8A087003206840,
    0x35680911845042802482700005201125D9004500483F8480608065D93859386E04A07202000,
    0x622D80100001000828010110820081F63B004530080CC410A0080510A004C1A021104190080,
    0x40480080A808088128C00000A0240940ABF80C0320C80D8120040900A00400A130040983280,
)


CYCLIC_TAIL_FOREST_MASKS = (
    0x3068282000020590320290452084022651040E82403D01941A0064873011D88086A03306A48,
    0x256C00115C5043600000B0490400912558245D00403D8410048945992858006E07307306208,
    0x42180900001000028098190A22881F61D0005100804C410AC084110A00CC52001004190280,
    0x60410000A8091880A8C00080A00419438BF80CA300C0050120840900A00C012200000983200,
)


def reflected_head_negative(original):
    m = REFLECTION_MULTIPLIER
    assert m % 13 == 12 and m % 23 == 1 and m * m % N == 1
    return tuple(tuple(w[m * i % N] for i in range(N)) for w in original[:2]) + original[2:]


def cyclic_tail_negative(original):
    a, b, c, d = map(word, ("+.-+-..++......", "......+..---+--", "+---+-..-", "+-..---.+"))
    e, f = [0] * N, [0] * N
    for i, (x, y) in enumerate(zip(a, b, strict=True)):
        for j, (u, v) in enumerate(zip(c, d, strict=True)):
            e[(32 * i + j) % N] += x * u
            e[(32 * i + 8 - j) % N] += y * v
            f[(32 * i + j) % N] += x * v
            f[(32 * i + 8 - j) % N] -= y * u
    assert all(x in (-1, 0, 1) for x in e + f)
    assert periodic((e, f)) == [169] + [0] * (N - 1)
    assert all(e[i] * f[(39 - i) % N] == 0 for i in range(N))
    tail = (tuple(e[i] + f[(39 - i) % N] for i in range(N)),
            tuple(f[i] - e[(39 - i) % N] for i in range(N)))
    assert periodic(tail) == [338] + [0] * (N - 1)
    return original[:2] + tail


def positive_words(negative, masks):
    result = []
    for row, mask in zip(negative, masks, strict=True):
        assert mask >> N == 0
        assert all(not (mask >> i & 1) or value == 0 for i, value in enumerate(row))
        result.append(tuple(0 if value else (1 if mask >> i & 1 else -1)
                            for i, value in enumerate(row)))
    return tuple(result)


def independent_dihedral(a, b):
    first, second = tuple(map(bool, a)), tuple(map(bool, b))
    return any(all(first[i] == second[(offset + direction * i) % N] for i in range(N))
               for offset in range(N) for direction in (-1, 1))


def verify(original, negative, masks, distances, dihedral, metrics, mod32, mod64):
    assert all(value in (-1, 0, 1) for row in negative for value in row)
    assert periodic(negative) == [599] + [0] * (N - 1)
    assert all(len(row) == N for row in negative)
    assert tuple(sum(bool(x) != bool(y) for x, y in zip(a, b, strict=True))
                 for a, b in zip(original, negative, strict=True)) == distances
    assert tuple(independent_dihedral(a, b)
                 for a, b in zip(original, negative, strict=True)) == dihedral
    positive = positive_words(negative, masks)
    assert tuple(map(sum, positive)) == (0, 1, 0, 0)
    e = replay(positive, negative, metrics, mod32, metrics[2] // 8)
    assert 1 + 2 * sum(a % 8 == 0 for a in e[1:]) == mod64
    return e


def main():
    original = nested_negative_words()
    verify(original, reflected_head_negative(original), REFLECTED_HEAD_MASKS,
           (120, 112, 0, 0), (True, True, True, True), (293, 89, 48, 316416), 181, 89)
    print("Partial head CRT reflection: exact T, C13, C23 and all raw mod8; 293 mod16, 89 exact.")
    tail = cyclic_tail_negative(original)
    tail_distances = (0, 0, 144, 142)
    tail_orbits = (True, True, False, False)
    verify(original, tail, CYCLIC_TAIL_MASKS, tail_distances, tail_orbits,
           (461, 129, 80, 536064), 233, 149)
    print("Changed cyclic tail supports: exact T, C13, C23 and all raw mod8; 461 mod16, 129 exact.")
    e = verify(original, tail, CYCLIC_TAIL_FOREST_MASKS, tail_distances, tail_orbits,
               (381, 89, 48, 289280), 177, 89)
    high = tuple(i for i in range(1, 150) if abs(e[i]) >= 5)
    assert high == (17, 26, 30, 35, 57, 69, 80, 87, 131, 133, 136)
    assert forest(high)[1] == ()
    check_factors()
    counts = tuple(sum(bool(v) for v in remainder(e, g, 5)) for g in FACTORS_5)
    assert counts == (32, 39, 38)
    print("Changed cyclic tail supports: peak48, 381 mod16, 89 exact, modulus-5 forest;",
          "nonzero primitive coefficients", counts)


if __name__ == "__main__":
    main()
