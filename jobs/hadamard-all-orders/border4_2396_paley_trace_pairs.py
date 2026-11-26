"""Replay a trace-44 hit obtained by joining four actual row-pair swaps."""

from border4_2396_paley_dual_integer import audit_signs
from border4_2396_paley_negative_norm import N, multiply, periodic, remainder, sign_word
from border4_2396_paley_q13_mod16 import margins
from border4_2396_paley_relative_trace_gate import trace44
from border4_2396_paley_reselected_heads import FIXTURES

PAIRS = ((0, 4), (2, 7), (6, 11), (8, 12))
COLUMNS = (1212592, 665609, 737410, 98464)
PHI13 = (1 << 13) - 1


def frobenius(value, exponent):
    for _ in range(exponent):
        value = remainder(multiply(value, value), PHI13)
    return value


def pairing(a, b):
    value = remainder(multiply(a, frobenius(b, 6)), PHI13)
    return value ^ frobenius(value, 4) ^ frobenius(value, 8)


def main():
    assert len({x for pair in PAIRS for x in pair}) == 8
    masks = tuple((1 << x) | (1 << y) for x, y in PAIRS)
    crossings = {pairing(masks[i], masks[j]) for i in range(2) for j in range(2, 4)}
    crossings.update(pairing(masks[j], masks[i]) for i in range(2) for j in range(2, 4))
    assert crossings == {0, 2533}
    assert frobenius(2533, 4) == 2533
    u, v, w = map(sign_word, FIXTURES[0][0])
    changed = list(w)
    for (x, y), columns in zip(PAIRS, COLUMNS, strict=True):
        for j in range(23):
            if columns >> j & 1:
                a, b = (92*x+208*j) % N, (92*y+208*j) % N
                assert changed[a] == -changed[b]
                changed[a], changed[b] = changed[b], changed[a]
    assert sum(x != y for x, y in zip(w, changed, strict=True)) == 44
    assert all(margins((w,), q) == margins((changed,), q) for q in (13, 23))
    raw = audit_signs(u, v, tuple(changed), (17, -5, -21))
    assert (max(map(abs, raw)), sum(x*x for x in raw), raw.count(0),
            sum(x % 16 == 0 for x in raw), sum(x % 24 == 0 for x in raw)) == (
                64, 444928, 57, 285, 209)
    residual = periodic((u, v, changed, changed))
    residual[0] -= 1196
    assert all(x % 8 == 0 for x in residual) and not trace44(tuple(x//8 for x in residual))
    print("Four row pairs: 44 physical flips, complete relative trace zero, raw peak 64, SSE 444928")


if __name__ == "__main__":
    main()
