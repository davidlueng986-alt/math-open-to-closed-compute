"""Replay an exact C23 obstruction for the early physical primitive F3 hit."""

from math import isqrt

from border4_2396_dual_mod5_forest import reciprocal
from border4_2396_paley_dual_integer import real_norm, required_tail
from border4_2396_paley_negative_norm import N, paley_words, periodic, sign_word
from border4_2396_paley_peak32_gates import FACTORS_3, check_factors_3
from border4_2396_primitive_field import remainder

MASKS = (
    0xA7AF19DBBD8D63C1561521CEC50A58441DD895CF560B64F1471336170C1D235981E1DF406C,
    0x687752F2CE282CF808D0B9B6DDC21A3248787305F3BF62D7D12C4BBAF2F422CF777246F0638,
    0x335EE1BD12B6C784A80E7CF7BA56D04E4C72D570CE26ECB0E3CBA3442CFE7EDE303FCF2A1B7,
)
FACTOR = tuple(map(int, "2121012021112000000121112012100001"))


def verify():
    check_factors_3()
    assert FACTOR in FACTORS_3 or reciprocal(FACTOR, 3) in FACTORS_3
    u, v, w = tuple(map(sign_word, MASKS))
    skew, d = paley_words()
    shifted = d[-8:] + d[:-8]
    assert all(a*b == -x*y for a, b, x, y in zip(u, v, d, shifted, strict=True))
    assert tuple(map(sum, (u, v, w))) == (17, -5, -21)
    e = periodic((u, v, w, w))
    e[0] -= 1196
    assert not e[0] and all(value % 8 == 0 for value in e)
    assert all(sum(e[i::13]) == 0 for i in range(13))
    assert not any(remainder(tuple(e), FACTOR, 3))
    assert not any(remainder(tuple(e), reciprocal(FACTOR, 3), 3))
    raw = tuple((-1)**i * e[i % N] for i in range(1, 2*N))
    assert (sum(value % 16 == 0 for value in raw), raw.count(0),
            max(map(abs, raw)), sum(value**2 for value in raw)) == (261, 37, 112, 927744)
    norm = abs(real_norm(required_tail(u, v)))
    prime = 229
    assert all(prime % divisor for divisor in range(2, isqrt(prime) + 1))
    assert prime % 23 == 22 and norm % prime == 0 and norm % (prime*prime) != 0
    assert norm == 359883084565553369621 == 139*229*1979*5713014908329
    print(f"Physical C13 and F3 hit: fixed heads have odd normalized C23 norm valuation at {prime}")


if __name__ == "__main__":
    verify()
