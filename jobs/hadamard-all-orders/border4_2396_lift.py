"""Check a width-four simultaneous sign lift and the exact length-26 quotient."""

from border4_2396 import periodic


SIZE = 299
FULL = (1 << SIZE) - 1
SUPPORT_A = 0x47D7EC8D55EC85DD1DBD2BA102D624CCD4BAB083B3C44A834656AEEE91B345FE9ED6052304B
SUPPORT_B = 0x406640D16591F4AA1CD91D8C5F5F4E9363B53FCADC6C972FAFA31B89B38552F89A68B026602
NEGATIVE_S = (
    0x440AC8854E8849C10202A2102402008441A808282C4028342448A0C1022055E04100122009,
    0x4142E085504484C51DA4030000D4004C84A88080100442034614A2C09023401410D00003042,
    0x402240510400108A08810C800C53421203B53E8884441604A7800100838402488A601024002,
    0x400400D10591B00804C11D084A084C1061B119C89824050F05200109B280105800002004001,
)
NEGATIVE_T = (
    0x28201010820118228002141CA420133003410A500829815880A91010044498000100D008494,
    0x8133088003020620010084501C230000145004808A510112941100E0038010029F81CFB4,
    0x2018220880440B50C104421180A0A1440800C024209120804044640608228804219100481CD,
    0x17109E2818260B114202E240A080A06400408014238168C0101C241400728C0641860F00820,
)


def signed(supports, negatives):
    words = []
    for support, negative in zip(supports, negatives, strict=True):
        assert support & ~FULL == 0 and negative & ~support == 0
        words.append(tuple(((support >> index) & 1) - 2 * ((negative >> index) & 1)
                           for index in range(SIZE)))
    return tuple(words)


def compress(words, size):
    assert all(len(word) % size == 0 for word in words)
    return tuple(tuple(sum(word[residue::size]) for residue in range(size)) for word in words)


def verify():
    assert SUPPORT_B & 1 == 0
    assert all((SUPPORT_B >> index & 1) == (SUPPORT_B >> (SIZE - index) & 1)
               for index in range(1, SIZE))
    support_s = (SUPPORT_A, SUPPORT_A, SUPPORT_B, SUPPORT_B | 1)
    support_t = tuple(FULL ^ support for support in support_s)
    assert tuple(mask.bit_count() for mask in support_s) == (150, 150, 148, 149)
    s = signed(support_s, NEGATIVE_S)
    t = signed(support_t, NEGATIVE_T)
    assert tuple(map(sum, s)) == (0, 0, 0, 1)
    assert tuple(map(sum, t)) == (15, 7, 15, -10)
    assert sum(sum(word)**2 for word in t) == 599

    residual_s = [value + 2 for value in periodic(s)]
    residual_t = periodic(t)
    residual_s[0] -= 599
    residual_t[0] -= 599
    assert all(value % 4 == 0 for value in residual_s + residual_t)
    assert residual_s[0] == residual_t[0] == 0
    assert tuple(sum(value == 0 for value in values[1:150])
                 for values in (residual_s, residual_t)) == (21, 19)
    assert tuple(sum(value**2 for value in values[1:150])
                 for values in (residual_s, residual_t)) == (23424, 25344)
    assert periodic(compress(s, 13)) == [553] + [-46] * 12
    assert periodic(compress(t, 13)) == [599] + [0] * 12

    words = tuple(tuple(left[i % SIZE] + (-1)**(i % 2) * right[i % SIZE]
                        for i in range(2 * SIZE))
                  for left, right in zip(s, t, strict=True))
    assert all(set(word) == {-1, 1} for word in words)
    correlations = periodic(words)
    assert correlations[0] == 2392 and correlations[299] == -4
    assert all((value + 4) % 8 == 0 for value in correlations[1:])
    assert periodic(compress(words, 26)) == [2304] + [-92] * 25
    exact = sum(value == -4 for value in correlations[1:])
    assert exact == 69
    print(f"width four / 2396: all 597 off-diagonal shifts mod 8; {exact} exactly -4")
    print("width four / 2396: exact length-26 quotient, including both length-13 sign halves")


if __name__ == "__main__":
    verify()
