"""Replay physical primitive F3 pairs and nine selected orbit parities."""

from math import gcd

from border4_2396_dual_mod5_forest import reciprocal
from border4_2396_paley_dual_integer import audit_signs
from border4_2396_paley_negative_norm import N, paley_words, periodic, sign_word
from border4_2396_paley_peak32_gates import FACTORS_3
from border4_2396_paley_q13_mod16 import margins
from border4_2396_paley_relative_trace_gate import PROJECTED_TRACE_LAGS
from border4_2396_paley_reselected_heads import FIXTURES as HEAD_FIXTURES
from border4_2396_primitive_field import remainder

ORBITS = tuple(representative for representative, _ in PROJECTED_TRACE_LAGS)
FIXTURES = (
    (0, 235, 0x381FBAD2B3C3F3CFC38D4955E81D408667DAD2E8DA2C6E597D5B57D36EC68B6AF16BF4CC304,
     (301, 33, 144, 1117696)),
    (3, 293, 0x419B353C69D9DB9B923C8C588211FF3B6D210F99CD0FC3973BBBDD3A7C16733E149E5B9FF2,
     (301, 57, 96, 901632)),
)


def relabel(word, multiplier):
    return tuple(word[multiplier*i % N] for i in range(N))


def exact_pairs(error):
    forward = tuple(i for i, f in enumerate(FACTORS_3) if not any(remainder(error, f, 3)))
    backward = tuple(i for i, f in enumerate(FACTORS_3)
                     if not any(remainder(error, reciprocal(f, 3), 3)))
    assert forward == backward
    return forward


def replay(factor, multiplier, encoded_tail):
    (u, v, reference), _, _, _ = HEAD_FIXTURES[2]
    u, v, reference, w = map(sign_word, (u, v, reference, encoded_tail))
    assert all(margins((w,), q) == margins((reference,), q) for q in (13, 23))
    raw = audit_signs(u, v, w, (17, -5, -21))
    error = periodic((u, v, w, w))
    error[0] -= 1196
    assert exact_pairs(error) == (factor,)
    assert gcd(multiplier, N) == 1
    assert pow(139, 2, N) == 185 and pow(139, 3, N) == 1

    skew, d = paley_words()
    shifted = d[-8:] + d[:-8]
    sum_half = (skew, tuple((a+b)//2 for a, b in zip(d, shifted, strict=True)),
                tuple((a-b)//2 for a, b in zip(d, shifted, strict=True)), (0,) * N)
    diff_half = ((1,) + (0,) * (N-1), tuple((a+b)//2 for a, b in zip(u, v, strict=True)),
                 tuple((a-b)//2 for a, b in zip(u, v, strict=True)), w)
    sum_half = tuple(relabel(row, multiplier) for row in sum_half)
    diff_half = tuple(relabel(row, multiplier) for row in diff_half)
    assert periodic(sum_half) == [597] + [-2] * (N-1)
    for q in (13, 23):
        assert periodic(margins(diff_half, q)) == [599] + [0] * (q-1)
    assert all(a*a+b*b == 1 for s, t in zip(sum_half, diff_half, strict=True)
               for a, b in zip(s, t, strict=True))
    words = tuple(tuple(s[i % N] + (-1)**i * t[i % N] for i in range(2*N))
                  for s, t in zip(sum_half, diff_half, strict=True))
    assert all(abs(value) == 1 for row in words for value in row)
    assert tuple(map(sum, words)) == (0, 2, 0, 0)
    renamed_error = periodic(tuple(relabel(row, multiplier) for row in (u, v, w, w)))
    renamed_error[0] -= 1196
    assert tuple(renamed_error) == relabel(error, multiplier)
    assert len(exact_pairs(renamed_error)) == 1
    sums = tuple(sum(renamed_error[d*m % N] for m in (1, 139, 185)) for d in ORBITS)
    assert not any(value % 16 for value in sums)

    renamed_raw = tuple(value + 4 for value in periodic(words)[1:])
    assert not any(value % 8 for value in renamed_raw)
    assert renamed_raw == tuple((-1)**i * renamed_error[i % N]
                               for i in range(1, 2*N))
    statistics = (sum(e % 16 == 0 for e in raw), raw.count(0), max(map(abs, raw)),
                  sum(e*e for e in raw))
    renamed_statistics = (sum(e % 16 == 0 for e in renamed_raw), renamed_raw.count(0),
                          max(map(abs, renamed_raw)), sum(e*e for e in renamed_raw))
    assert statistics == renamed_statistics
    return exact_pairs(renamed_error)[0], sums, statistics


def main():
    for factor, multiplier, tail, expected in FIXTURES:
        final_factor, sums, statistics = replay(factor, multiplier, tail)
        assert final_factor == 2 and statistics == expected
        print(f"One primitive F3 pair {final_factor}, multiplier {multiplier}, "
              f"nine folded sums {sums}, raw {statistics}")


if __name__ == '__main__':
    main()
