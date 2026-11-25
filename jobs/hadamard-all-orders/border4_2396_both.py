"""Replay the common sign lift for the exact length-26 and length-46 quotients."""

from border4_2396 import periodic
from border4_2396_lift import FULL, SIZE, compress, signed


SUPPORT_A = 0x379134DDFC4F223A02DCDB7FFA67835595C76F223D03D43F4CB46419348A72CB034D27881CC
SUPPORT_B = 0x3F853C61E93D0A2921C61E565CA5C43D31DFB0DFB8CBC23A53A6A7863849450BC97863CA1FC
NEGATIVE_S = (
    0x14110058780C000A02185A7BDA65825404C044020401940508100008208A4248010D240004C,
    0x171104596C0E2208021CCA515227024005400C02040100050834400934803240010C240014C,
    0x1D001840E83C0000218410001C24C00131DBB0DD80C800221304800600400508890820420D8,
    0xB811001E1290000200416425824800520CB0045800902304022A2041849450888386242158,
)
NEGATIVE_T = (
    0x40624900022014C56C20008001107008202010810288238021010A04821089300882D813213,
    0x404A8B220110084558020000010004084808004542D4284011421AC64961810024B0D072420,
    0x2438A068200149E298088A3022180C2204B2042100881005800318210A03412810801002,
    0x4052420A064260D29628A0A8A012180000204F2043200D84245150508606A8E420861820800,
)

# Each triple is (constant, quadratic-character coefficient, coefficient at zero).
PROFILES = {
    13: (
        ((0, -3, 0), (0, -1, 0), (0, -6, 0), (0, 0, 1)),
        ((1, -1, 2), (1, 3, -6), (1, 4, 2), (-1, 4, 3)),
    ),
    23: (
        ((0, -3, 0), (0, -3, 0), (0, -2, 0), (0, -2, 1)),
        ((1, -3, -8), (0, 0, 7), (1, -2, -8), (0, -1, -10)),
    ),
}


def verify_residual_coordinates():
    def fold(index, p):
        return min(index % p, -index % p)

    edges = [(fold(d, 13), fold(d, 23)) for d in range(1, (SIZE + 1) // 2)]
    assert set(edges) == {(a, b) for a in range(7) for b in range(12)} - {(0, 0)}
    # A spanning tree uses the first two stars and attaches the right zero vertex.
    tree = {(0, b) for b in range(1, 12)} | {(a, 1) for a in range(1, 7)} | {(1, 0)}
    remaining = list(edges)
    for edge in tree:
        remaining.remove(edge)
    assert len(tree) == 18 and len(remaining) == 131


def verify():
    assert SUPPORT_B & 1 == 0
    assert all((SUPPORT_B >> i & 1) == (SUPPORT_B >> (SIZE - i) & 1) for i in range(1, SIZE))
    support_s = (SUPPORT_A, SUPPORT_A, SUPPORT_B, SUPPORT_B | 1)
    support_t = tuple(FULL ^ support for support in support_s)
    assert tuple(mask.bit_count() for mask in support_s) == (150, 150, 148, 149)
    s, t = signed(support_s, NEGATIVE_S), signed(support_t, NEGATIVE_T)
    assert tuple(map(sum, s)) == (0, 0, 0, 1)
    assert tuple(map(sum, t)) == (15, 7, 15, -10)
    for p, (s_profile, t_profile) in PROFILES.items():
        squares = {i*i % p for i in range(1, p)}
        character = (0,) + tuple(1 if x in squares else -1 for x in range(1, p))
        for words, profile, off in ((s, s_profile, -598 // p), (t, t_profile, 0)):
            projected = tuple(tuple(constant + amplitude * char + spike * (i == 0)
                                    for i, char in enumerate(character))
                              for constant, amplitude, spike in profile)
            assert compress(words, p) == projected
            assert periodic(projected) == [599 + off] + [off] * (p - 1)
    for words, off in ((s, -2), (t, 0)):
        residual = [value - off for value in periodic(words)]
        assert residual[0] == 599 and all(value % 4 == 0 for value in residual[1:])
    binary = tuple(tuple(a[i % SIZE] + (-1)**(i % 2) * b[i % SIZE] for i in range(2 * SIZE))
                   for a, b in zip(s, t, strict=True))
    assert all(set(word) == {-1, 1} for word in binary)
    correlations = periodic(binary)
    assert correlations[0] == 2392 and correlations[SIZE] == -4
    assert all((value + 4) % 8 == 0 for value in correlations[1:])
    assert sum(value == -4 for value in correlations[1:]) == 47
    assert max(abs(value + 4) for value in correlations[1:]) == 136
    for size in (26, 46):
        off = -2392 // size
        assert periodic(compress(binary, size)) == [2396 + off] + [off] * (size - 1)
    verify_residual_coordinates()
    print("width four / 2396: exact 26- and 46-point quotients on one full modulo-eight witness")
    print("width four / 2396: 47 exact original off-diagonal shifts, 131 sufficient errors per half")


if __name__ == "__main__":
    verify()
