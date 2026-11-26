"""Replay the degree-44 relative trace gate on the reselected Paley heads."""

from border4_2396_dual_mod5_forest import forest
from border4_2396_paley_dual_integer import audit_signs
from border4_2396_paley_negative_norm import DIRECTED_PAIRS, N, periodic, sign_word
from border4_2396_paley_negative_norm import remainder as binary_remainder
from border4_2396_paley_peak32_gates import FACTORS_3, check_factors_3
from border4_2396_paley_q13_mod16 import margins
from border4_2396_paley_reselected_heads import FIXTURES
from border4_2396_primitive_field import remainder


def inverse_class(d, modulus):
    return min(d % modulus, -d % modulus)


def trace44(e):
    return sum(((e[d] + e[139*d % N] + e[185*d % N]) % 2) << d for d in range(N))


def prove_trace_gate():
    masks, expected, _, _ = FIXTURES[1]
    u, v, w = tuple(map(sign_word, masks))
    raw = audit_signs(u, v, w, (17, -5, -21))
    assert (sum(a % 16 == 0 for a in raw), raw.count(0), max(map(abs, raw)),
            sum(a*a for a in raw)) == expected == (277, 117, 32, 119808)
    residual = periodic((u, v, w, w))
    residual[0] -= 1196
    assert not residual[0] and all(value % 8 == 0 for value in residual)
    assert all(sum(residual[i::q]) == 0 for q in (13, 23) for i in range(q))

    frobenius_orbit = {pow(2, i, N) for i in range(132)}
    assert len(frobenius_orbit) == 132 and N - 1 not in frobenius_orbit
    assert pow(2, 132, N) == 1
    multiplier = pow(2, 44, N)
    assert multiplier == 139 and pow(multiplier, 2, N) == 185
    assert pow(multiplier, 3, N) == 1 and multiplier % 13 == 9 and multiplier % 23 == 1
    high = {d for d in range(1, 150) if abs(residual[d]) >= 24}
    assert len(high) == 25

    selected = ((3, 43), (7, 7), (10, 10), (11, 11), (16, 30),
                (22, 22), (23, 69), (25, 113), (48, 48))
    for representative, unique in selected:
        orbit = {inverse_class(representative * pow(multiplier, i, N), N) for i in range(3)}
        assert representative == min(orbit) and orbit & high == {unique}
    remainder_lags = high.difference(unique for _, unique in selected)
    tree, chords = forest(sorted(remainder_lags))
    assert len(tree) == 16 and not chords
    assert len(forest(sorted(high))[1]) == len(selected) == 9
    print("Projected trace: nine selected orbit parities remove nine edges, leaving a 16-edge forest")
    survivors = tuple(d for d in sorted(high)
                      if len({inverse_class(d * pow(multiplier, i, N), N)
                              for i in range(3)} & high) > 1)
    assert survivors == (2, 21, 71)
    edges = tuple((inverse_class(d, 13), inverse_class(d, 23)) for d in survivors)
    assert edges == ((2, 2), (5, 2), (6, 2))
    assert len({x for x, _ in edges}) == 3  # each remains alone in its C13 inverse class

    # The source supplies the envelope but still fails both arithmetic inputs.
    e = tuple(value // 8 for value in residual)
    factor = next(p for p in DIRECTED_PAIRS if p.bit_length() == 133)
    assert binary_remainder(trace44(e), factor)
    check_factors_3()
    assert any(any(remainder(e, p, 3)) for p in FACTORS_3)
    print("Relative degree-44 trace: 25 high lags reduce to (2, 21, 71), each alone in C13")


def verify_physical_trace():
    (u, v, before), _, _, _ = FIXTURES[0]
    mask = 0x437B8E46D7CEF0511AACF87D9379506983425DD9CDA87661AA9313D3DEE7BFDD8E41C5626DD
    u, v, w, anchor = map(sign_word, (u, v, mask, before))
    for q in (13, 23):
        assert margins((w,), q) == margins((anchor,), q)
    raw = audit_signs(u, v, w, (17, -5, -21))
    assert (sum(a % 16 == 0 for a in raw), raw.count(0), max(map(abs, raw)),
            sum(a*a for a in raw)) == (301, 77, 88, 723456)
    e = periodic((u, v, w, w))
    e[0] -= 1196
    assert all(value % 8 == 0 for value in e)
    assert trace44(tuple(value // 8 for value in e)) == 0
    print("Physical exact-dual signs: complete degree-44 trace zero, peak 88")


if __name__ == "__main__":
    prove_trace_gate()
    verify_physical_trace()
