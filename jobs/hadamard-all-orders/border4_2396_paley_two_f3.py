"""Replay physical signs with two complete primitive F3 factor pairs."""

from math import gcd

from border4_2396_paley_negative_norm import N, paley_words, periodic, sign_word
from border4_2396_paley_projected_f3 import ORBITS, exact_pairs, relabel
from border4_2396_paley_q13_mod16 import margins
from border4_2396_paley_reselected_heads import FIXTURES as HEADS

# Source and final primitive pairs, inverse-index multiplier, physical W mask,
# Raw statistics are mod-16 zeros, integer zeros, peak, square residual and mod-24 zeros.
FIXTURES = (
    ((0, 2), (0, 2), 27, 0x3FF818FDBFBCDE29A9F1820C15E1FF1CCE584AD33B2702B70F221B2A38FD478956BDB625EBA,
     (325, 65, 72, 500736, 177), (64, 48, 16, 16, 0, -64, 0, 16, -16)),
    ((1, 3), (1, 3), 64, 0x7D7A85420270483E268A685D7F6806DD85A64B79CF5B0C9AA37677FB9CBE2C59EE5B99F27BD,
     (309, 81, 72, 527360, 217), (-16, 48, -16, -64, -64, -16, 48, 32, -32)),
    ((1, 3), (0, 2), 85, 0x15AE2C57229A2A5BA9ADFBFDA018FF2B64F05F5D7A5BF5DC1BBA84AD6C1A76047DCC586BA45,
     (293, 57, 72, 726016, 245), (-16, -16, 96, -64, -80, 16, -96, -16, 64)),
)


def halves(u, v, w):
    skew, d = paley_words()
    ds = d[-8:] + d[:-8]
    positive = (skew, tuple((a+b)//2 for a,b in zip(d,ds,strict=True)),
                tuple((a-b)//2 for a,b in zip(d,ds,strict=True)), (0,) * N)
    negative = ((1,) + (0,) * (N-1), tuple((a+b)//2 for a,b in zip(u,v,strict=True)),
                tuple((a-b)//2 for a,b in zip(u,v,strict=True)), w)
    return positive, negative


def replay(original, final, multiplier, tail):
    umask, vmask, wmask = HEADS[2][0]
    u, v, reference, w = map(sign_word, (umask, vmask, wmask, tail))
    assert tuple(map(sum, (u, v, w))) == (17, -5, -21)
    for q in (13, 23):
        (base,), (target,) = margins((reference,), q), margins((w,), q)
        assert any(target == base[i:] + base[:i] for i in range(q))
    residual = periodic((u, v, w, w))
    residual[0] -= 1196
    assert exact_pairs(residual) == original
    assert gcd(multiplier, N) == 1
    positive, negative = halves(u, v, w)
    positive = tuple(relabel(row, multiplier) for row in positive)
    negative = tuple(relabel(row, multiplier) for row in negative)
    assert periodic(positive) == [597] + [-2] * (N-1)
    for q in (13, 23):
        assert periodic(margins(negative, q)) == [599] + [0] * (q-1)
    assert all(a*a+b*b == 1 for s,t in zip(positive,negative,strict=True)
               for a,b in zip(s,t,strict=True))
    words = tuple(tuple(s[i % N] + (-1)**i*t[i % N] for i in range(2*N))
                  for s,t in zip(positive,negative,strict=True))
    assert all(abs(a) == 1 for row in words for a in row)
    assert tuple(map(sum, words)) == (0, 2, 0, 0)
    raw = tuple(v + 4 for v in periodic(words)[1:])

    moved_u,moved_v,moved_w = (relabel(row, multiplier) for row in (u,v,w))
    moved = periodic((moved_u,moved_v,moved_w,moved_w))
    moved[0] -= 1196
    assert tuple(moved) == relabel(residual,multiplier)
    assert all(value % 8 == 0 for value in moved)
    assert raw == tuple((-1)**i * moved[i % N] for i in range(1, 2*N))
    assert exact_pairs(moved) == final
    sums = tuple(sum(moved[d*m % N] for m in (1,139,185)) for d in ORBITS)
    raw_stats = (sum(x % 16 == 0 for x in raw), raw.count(0), max(map(abs,raw)),
                 sum(x*x for x in raw), sum(x % 24 == 0 for x in raw))
    return raw_stats,sums


def main():
    for original, final, multiplier, tail, expected, expected_sums in FIXTURES:
        raw,sums = replay(original,final,multiplier,tail)
        assert raw == expected and sums == expected_sums
        assert not any(a % 16 for a in sums)
        print(f"F3 pairs {final}, nine projected parities, multiplier {multiplier}: {raw}")


if __name__ == '__main__':
    main()
