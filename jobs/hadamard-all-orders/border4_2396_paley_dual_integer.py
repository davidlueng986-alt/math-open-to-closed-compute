"""Replay exact Paley positive and dual-integer-quotient negative halves."""

from math import isqrt
from random import Random

from border4_2396_paley_negative_norm import N, paley_words, periodic, sign_word
from border4_2396_paley_q13_mod16 import margins
from verify import determinant

Q = 23
W_13 = (3, -9, -9, 7, -9, 1, -1, 1, -3, -5, -3, 3, 3)
FIXTURES = (
    (
        95024,
        0x20E891FCBF070476112B5BB12C64BA4B43F01218FA5F348F2F28364375E56D87907E7961400,
        0x42E53293CAF7FEB20C9AB01B1DF605FD4A55E841FC80E017EA754E98F7D09D7D7F122265254,
        (-3, -1, 7, -5, 1, -1, -3, -1, -1, 1, -9, 3, 1, -1, -5, -5, -1, 5, 1, 1, -3, -1, -1),
        (17, -5, -21),
        (317, 49, 96, 792064),
    ),
    (
        95030,
        0x3BA32522030A9B15EB2B8551B4351800BFB97B3B077B6C2EBF5F8646898AF68447CCA44CDC7,
        0x59AE864D76FA61D1F69A6EFB85A7A7B6B61C816201A4B8B67A02FE9D0BBF067EA8A0FF48B93,
        (-11, -5, 7, -1, -3, 7, -5, 1, -7, 3, 3, -1, -1, -3, 1, 1, 5, -1, -3, -1, -1, -3, -3),
        (5, -17, -21),
        (293, 37, 96, 910336),
    ),
    (
        95034,
        0x687027E1E7ADFEc20FC0F8F14D75C3BD3346E4C81CA6DC074F046B34F73098D63BF8A8F0692,
        0xA7D848E925D04061271135B7CE77C0B3AE31E911A79089F8A5913EF7505682CD494F3F40C6,
        (-9, 5, -1, -1, -1, 1, -1, -3, -1, 5, -3, 1, 1, -3, -3, 11, -1, 1, -3, -3, -1, -5, -7),
        (-5, 17, -21),
        (341, 73, 112, 995328),
    ),
)


def physical_word(row_sums, column_sums, seed):
    assert all(-23 <= value <= 23 and value % 2 for value in row_sums)
    assert all(-13 <= value <= 13 and value % 2 for value in column_sums)
    row_degrees = tuple((23 - value) // 2 for value in row_sums)
    capacity = [(13 - value) // 2 for value in column_sums]
    assert sum(row_degrees) == sum(capacity)
    ordered = sorted(row_degrees, reverse=True)
    for width in range(1, 14):
        assert sum(ordered[:width]) <= sum(min(width, degree) for degree in capacity)
    rows, columns = list(range(13)), list(range(23))
    random = Random(seed)
    random.shuffle(rows)
    rows.sort(key=row_degrees.__getitem__, reverse=True)
    word = [1] * N
    for x in rows:
        random.shuffle(columns)
        columns.sort(key=capacity.__getitem__, reverse=True)
        for y in columns[:row_degrees[x]]:
            assert capacity[y] > 0
            capacity[y] -= 1
            i = (92 * x + 208 * y) % N
            assert i % 13 == x and i % 23 == y and word[i] == 1
            word[i] = -1
    assert not any(capacity)
    assert margins((word,), 13) == (row_sums,) and margins((word,), 23) == (column_sums,)
    return tuple(word)


def required_tail(u, v):
    head = periodic(margins((u, v), Q))
    head[0] -= 1196
    assert all(value % 2 == 0 for value in head)
    return tuple(-value // 2 for value in head)


def cyclotomic_reduction(word):
    # z^22 = -(1+z+...+z^21) for a primitive 23rd root.
    assert len(word) == Q
    return tuple(value - word[-1] for value in word[:-1])


def field_root_certificate(u, v, tail):
    required = cyclotomic_reduction(required_tail(u, v))
    word = cyclotomic_reduction(tail)
    assert all(value % 4 == 0 for value in required) and all(value % 2 == 0 for value in word)
    gamma = tuple(value // 2 for value in word) + (0,)
    assert cyclotomic_reduction(periodic((gamma,))) == tuple(value // 4 for value in required)


def polynomial_add(left, right):
    result = [0] * max(len(left), len(right))
    for i, value in enumerate(left):
        result[i] += value
    for i, value in enumerate(right):
        result[i] += value
    return result


def real_norm(word):
    # C_d(t)=z^d+z^(-d), t=z+z^(-1), and Psi_23(t)=1+sum C_d(t).
    trace = [[2], [0, 1]]
    for _ in range(2, 12):
        trace.append(polynomial_add([0] + trace[-1], [-x for x in trace[-2]]))
    modulus, alpha = [1], [word[0]]
    for d in range(1, 12):
        assert word[d] == word[-d]
        modulus = polynomial_add(modulus, trace[d])
        alpha = polynomial_add(alpha, [word[d] * value for value in trace[d]])
    assert modulus[-1] == 1 and len(modulus) == 12
    def reduce(poly):
        while len(poly) >= len(modulus):
            lead = poly[-1]
            offset = len(poly) - len(modulus)
            for i, value in enumerate(modulus):
                poly[offset + i] -= lead * value
            assert poly.pop() == 0
        return poly + [0] * (11 - len(poly))
    alpha = reduce(alpha)
    assert all(value % 4 == 0 for value in alpha)
    alpha = [value // 4 for value in alpha]
    matrix = [reduce([0] * i + alpha) for i in range(11)]
    return int(determinant(matrix))


def verify_inert_obstruction():
    # The two-error predecessor of fixture 95030 has a different fixed head.
    u, v = map(sign_word, (
        0x3BA32502030A9B15EB2B8551B4B51800ADB97B3F877B6C3EBF5F8646898AF684478CA44CDC7,
        0x59AE866D76FA61D1F69A6EFB8527A7B6A41C816681A4B8A67A02FE9D0BBF067EA8E0FF48B93,
    ))
    norm = abs(real_norm(required_tail(u, v)))
    prime = 108184961
    assert all(prime % d for d in range(2, isqrt(prime) + 1))
    assert prime % 23 == 22 and norm % prime == 0 and norm % (prime * prime) != 0
    assert norm == 217121 * 108184961 * 530819897
    print(f"Fixed predecessor: real norm has odd valuation at inert prime {prime}")


def verify_fixture(seed, u_mask, v_mask, w_23, sums, expected):
    u, v = map(sign_word, (u_mask, v_mask))
    w = physical_word(W_13, w_23, seed)
    assert tuple(map(sum, (u, v, w))) == sums
    field_root_certificate(u, v, w_23)
    skew, d = paley_words()
    shifted = d[-8:] + d[:-8]
    assert all(a * b == -c * e for a, b, c, e in zip(u, v, d, shifted, strict=True))
    positive = (skew, tuple((a+b)//2 for a, b in zip(d, shifted, strict=True)),
                tuple((a-b)//2 for a, b in zip(d, shifted, strict=True)), (0,) * N)
    negative = ((1,) + (0,) * (N-1), tuple((a+b)//2 for a, b in zip(u, v, strict=True)),
                tuple((a-b)//2 for a, b in zip(u, v, strict=True)), w)
    assert all(a*a + b*b == 1 for s, t in zip(positive, negative, strict=True)
               for a, b in zip(s, t, strict=True))
    assert periodic(positive) == [597] + [-2] * (N-1)
    for q in (13, 23):
        assert periodic(margins(negative, q)) == [599] + [0] * (q-1)
    words = tuple(tuple(s[i % N] + (-1)**i * t[i % N] for i in range(2*N))
                  for s, t in zip(positive, negative, strict=True))
    assert all(abs(value) == 1 for word in words for value in word)
    assert tuple(map(sum, words)) == (0, 2, 0, 0)
    raw = tuple(value + 4 for value in periodic(words)[1:])
    assert all(value % 8 == 0 for value in raw)
    stats = (sum(value % 16 == 0 for value in raw), raw.count(0),
             max(map(abs, raw)), sum(value*value for value in raw))
    assert stats == expected
    print(f"Exact positive half and both integer negative quotients, seed {seed}: {stats}")


if __name__ == "__main__":
    verify_inert_obstruction()
    for fixture in FIXTURES:
        verify_fixture(*fixture)
