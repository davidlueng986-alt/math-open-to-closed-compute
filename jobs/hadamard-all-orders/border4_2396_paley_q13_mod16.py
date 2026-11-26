"""Replay joint integer C13 and raw-mod16 Paley witnesses and their closure gate."""

from border4_2396_paley_negative_norm import N, audit, paley_words, periodic, reflect, shift, sign_word

ANCHOR = (
    0x27C75C0F34D8E836067D80169F2980902037EE0DE7B72150FF4256B9F1078A4B3BC0BF50AA,
    0x6071D6AF86BD74477DD633AB586027BF0BA684B9D8A4A68DCAA95DB01D25885E5CD050F16FE,
    0x3B8EFAF14E22F4AD3CC255CD888EDB5F5556753B7DF23C2B2C9C98D972855FBB49858F8E886,
)
AXIS_136 = (
    0x56B4B3CB3255E0E00B05FA86CF67A75727B7F003D9F001F06AA3BDBF400C9C4904BC57B000,
    0x6766E853C6D5A4CA1D01B4025D64C5C37BDE85593B40D487C3F743007635393E7F279E7F654,
    0x78F814D8DD12A3B1DBFF3E03FB007B93CC1103D74C2DBE3569A81E9D6EF51B7910C17F0D7F7,
)
AXIS_267 = (
    0x2262FFEDEB40D48350309B0EEC447C4E50191B64705904CF10F80BCB5F15D3A538F91C754AA,
    0x406F5C829EB02E474D8170A4DDD6C3F859BCE13D7686D057D5A57310DD20235FD79547712FE,
    0x19DCDFD35B4FFF1D0FCE551D834E5E92CB50F5B2AD4B2C3D2B07A2C94F85EFB845455285E2E,
)


def margins(rows, modulus):
    return tuple(tuple(sum(row[j::modulus]) for j in range(modulus)) for row in rows)


def residue_class(value, modulus):
    return min(value % modulus, -value % modulus)


def verify_profile():
    assert pow(7, 12, 13) == pow(7, 22, 23) == 1
    assert len({pow(7, d, 13) for d in range(12)}) == 12
    assert len({pow(7, d, 23) for d in range(22)}) == 22
    assert len({pow(7, d, N) for d in range(132)}) == 132
    assert pow(7, 132, N) == 1
    assert N-1 not in {pow(7, d, N) for d in range(132)}


def replay(physical_axis, masks, expected):
    du, dv, dw = (a^b for a,b in zip(ANCHOR,masks,strict=True))
    assert du == dv == shift(reflect(du),8)
    assert dw == shift(reflect(dw),physical_axis)
    rows = tuple(map(sign_word,masks))
    assert tuple(map(sum,rows)) == (17,-5,-21)
    assert margins(rows,13) == margins(tuple(map(sign_word,ANCHOR)),13)
    u,v,w = rows
    t = ((1,)+(0,)*(N-1),
         tuple((a+b)//2 for a,b in zip(u,v,strict=True)),
         tuple((a-b)//2 for a,b in zip(u,v,strict=True)),w)
    assert periodic(margins(t,13)) == [599]+[0]*12
    assert periodic(margins(t,23)) != [599]+[0]*22
    audit(paley_words(),8,masks,(1,6,11,-21),expected)
    e = periodic(rows+(w,))
    e[0] -= 1196
    assert all(x % 16 == 0 for x in e)
    assert all(sum(e[r::13]) == 0 for r in range(13))
    assert any((a-e[j%23]) % 7 for j,a in enumerate(e))
    return e


def main():
    verify_profile()
    e = replay(136,AXIS_136,(597,97,128,1056768))
    anchors = (93,71,95,4,189,29,7,8,285,56)
    assert all(e[r] == 0 and residue_class(r,23) == y
               for y,r in enumerate(anchors,1))
    assert tuple(d for d in range(1,150) if abs(e[d]) >= 112) == (1,113)
    assert {residue_class(d,13) for d in (1,113)} == {1,4}
    print("Axis 136: primitive mod7 suffices with the ten zero anchors and two exceptions")
    e = replay(267,AXIS_267,(597,85,96,897024))
    assert [j for j in range(1,12) if all(e[i] for i in range(j,N,23))] == [1,3]
    print("Axis 267: primitive mod7 plus one additional missing-class residue suffices at peak 96")


if __name__ == "__main__":
    main()
