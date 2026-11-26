"""Replay the Golay–Yang T(187) seed and its Paley progression."""

from math import comb, gcd, isqrt

from paley_progression import small_paley_blocks, verify_control
from t599_length_change import aperiodic, disjoint
from verify import signs


def golay_eight():
    left, right = (1,), (1,)
    for _ in range(3):
        left, right = left + right, left + tuple(-value for value in right)
    assert aperiodic((left, right)) == [16] + [0]*7
    return left, right


def yang_selectors(base_signs):
    """Specialize the Golay–Yang multiplication to a length-eight Golay pair."""
    a, b, c, d = tuple(map(signs, base_signs))
    m, n = len(a), len(c)
    assert len(b) == m and len(d) == n
    assert aperiodic((a, b, c, d)) == [2*(m + n)] + [0]*(max(m, n) - 1)
    f, g = golay_eight()
    zeros = (0,)*(m + n)

    def scale(word, sign):
        return tuple(sign*value for value in word)

    q, r, s, t = [], [], [], []
    for forward_f, reverse_f, forward_g, reverse_g in zip(f, f[::-1], g, g[::-1], strict=True):
        q.extend(scale(a, reverse_f) + scale(c, forward_g) + zeros)
        r.extend(scale(b, reverse_f) + scale(d, reverse_g) + zeros)
        s.extend(zeros + scale(a, reverse_g) + scale(c, -forward_f))
        t.extend(zeros + scale(b, forward_g) + scale(d, -forward_f))
    q.extend(scale(b[::-1], -1) + (0,)*n)
    r.extend(a[::-1] + (0,)*n)
    s.extend((0,)*m + scale(d[::-1], -1))
    t.extend((0,)*m + c[::-1])

    words = disjoint(q, r) + disjoint(s, t)
    length = (2*len(f) + 1)*(m + n)
    assert all(len(word) == length for word in words)
    assert aperiodic(words) == [length] + [0]*(length - 1)
    selectors = []
    for position in zip(*words, strict=True):
        assert sum(map(abs, position)) == 1
        selectors.append(sum((i + 1)*value for i, value in enumerate(position)))
    return tuple(selectors)


def verify_progression():
    p, width, period = 166_531_867, 187, 6_625_080
    modulus, target = 24_342_780, 20_018_009
    quotient = 4*modulus//11
    assert (modulus % 11, target % 11) == (0, 0)
    residue = (4*(target//11)*pow(17, -1, quotient) - 1) % quotient
    assert residue == 7_197_307 and gcd(residue, quotient) == 1

    extended = quotient*13*19*23*43*67*73
    assert extended == 10_576_169_147_303_760
    assert p % 8 == 3 and all(p % divisor for divisor in range(2, isqrt(p) + 1))
    assert p % quotient == residue and gcd(p, extended) == 1
    assert pow(p, period, extended) == 1
    t = width*((p + 1)//4)
    assert t == 7_785_364_829 and t % modulus == target
    assert (t % 13, t % 19, t % 23) == (8, 12, 0)
    assert all(t % prime for prime in (13, 19, 43, 67, 73))
    assert (16*t + 1) % 19 == 3 and all(value*value % 19 != 3 for value in range(19))
    print("T187 AP: prime 166531867, period 6625080, first multiplier 7785364829")


def verify():
    # HadamardR Basesequences, BaseOrder 5, four words in BaseMatrix order.
    selectors = yang_selectors(("+++-++", "+++-+-", "+++--", "+-++-"))
    assert len(selectors) == 187
    assert verify_control(selectors, small_paley_blocks()) == comb(3_740, 2) == 6_991_930
    verify_progression()


if __name__ == "__main__":
    verify()
