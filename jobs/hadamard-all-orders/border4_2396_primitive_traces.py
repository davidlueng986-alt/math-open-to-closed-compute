"""Replay physical simultaneous primitive trace witnesses modulo 3 and 5."""

from itertools import product

from border4_2396 import periodic
from border4_2396_adaptive_forest import EDGES, POSITIONS, forest, lags
from border4_2396_dual_changed_support import cyclic_tail_negative, positive_words
from border4_2396_dual_joint_geometry import change_second_head, raw_stats
from border4_2396_dual_mod5_forest import residual
from border4_2396_nested import nested_negative_words

N = 299
MOD3_MASKS = (
    0x4470028D09A47E03201D00D2025802311049800102101907228602D1041608883304303A00,
    0x780141340041E2063631208B209024010C10020AA72480840D20083041BA0853244B16F1A,
    0x2421801820000098A8018080820580363D44C0202C0C440088080518800C852001004590280,
    0x64098000CC188028451001A00409036B50050300880881A0840880288C012300000DA1080,
)
EXACT_MASKS = (
    0x41B0028909A47F83203100D25A5802811049800103D0190162860651041908881104301800,
    0x4C00418C0041C2063571A00E208024412E15024E9F2400C40C2078124182081244CB10B0B,
    0x4025801828000088A80D0000820980572944C4300C0C040808084100A00C84A0210445102C0,
    0x20680980200D088020C50001804509022F60048300800101A0C40880A88C002230200CA1280,
)
ORBIT_TRACE_MASKS = (
    0x47202098DA47601203900D2525022491049A82101505941A0040C51050C02883D04301000,
    0x10780041BC104162063431E00D608020C02A18024E972410E40420001201B2081304CB12B0B,
    0x2425801000010080A8018080820581F47D54C420080C4400AC080110800CC52000104190080,
    0x641980004D18810845100080050943794C050300880881A0440C80080C002300040D81008,
)
X_ORBITS = ((1, 3, 4), (2, 5, 6))


def real_order(p, q):
    a = p % q
    order = 1
    while a not in (1, q - 1):
        a = (a * p) % q
        order += 1
    return order


def check_periods():
    assert tuple(real_order(p, q) for p, q in product((3, 5), (13, 23))) == (
        3, 11, 2, 11)
    first = {a * a % 13 for a in range(1, 13)}
    second = set(range(1, 13)) - first
    assert first == {k % 13 for x in X_ORBITS[0] for k in (x, -x)}
    assert second == {k % 13 for x in X_ORBITS[1] for k in (x, -x)}
    product_coefficients = [0] * 13
    for x, y in product(first, second):
        product_coefficients[(x + y) % 13] += 1
    assert product_coefficients == [0] + [3] * 12


def check_transverse_trace(e):
    assert all(e[POSITIONS[x, 0]] == 0 for x in range(13))
    for p in (3, 5):
        multiplier = p ** real_order(p, 13)
        for x, y in product(range(13), range(23)):
            doubled_trace = sum(
                e[POSITIONS[x, y * pow(multiplier, j, 23) % 23]]
                + e[POSITIONS[x, -y * pow(multiplier, j, 23) % 23]]
                for j in range(11)
            )
            assert doubled_trace == (22 if y == 0 else -1) * e[POSITIONS[x, 0]]
            assert doubled_trace % p == 0


def x_traces(e):
    return tuple(
        all(sum(e[POSITIONS[x, y]] + e[POSITIONS[x, -y % 23]]
                for x in orbit) % 3 == 0 for y in range(23))
        for orbit in X_ORBITS
    )


def aggregate(e):
    return {edge: sum(e[i] for i in lags(edge)) for edge in EDGES}


def interior_failures(e):
    weights = aggregate(e)
    return tuple(sum(value % p != 0 for edge, value in weights.items()
                     if all(edge) and edge != (6, 11)) for p in (3, 5))


def check_peak56_gate(e):
    repairs = {(2, 6), (5, 6)}
    graphs = {1: set(), 2: set(), 4: set()}
    for edge in EDGES:
        cap = tuple(abs(e[i]) for i in lags(edge))
        if len(cap) == 1:
            values = range(3, cap[0] + 1, 3)
        else:
            a, b = cap
            values = {
                i + j for i, j in product(range(-a, a + 1), range(-b, b + 1))
                if (i - j) % 9 == 0 and i + j > 0 and (i + j) % 3 == 0
            }
        for value in values:
            graphs[value // 3].add(edge)
    assert tuple(len(graphs[j]) for j in (1, 2, 4)) == (12, 18, 0)
    assert len(forest(sorted(graphs[1]))) == 12
    assert len(forest(sorted(graphs[2]))) == 16
    assert repairs <= graphs[2]
    assert len(forest(sorted(graphs[2] - repairs))) == 16
    w = aggregate(e)
    assert all(w[edge] % 4 == 0 for edge in repairs)
    active = tuple(edge for edge in EDGES if edge[1])
    assert len(active) - len(forest(active)) == 60
    bad = sorted(edge for edge in active if w[edge] % 3)
    assert (len(bad), len(bad) - len(forest(bad))) == (37, 20)


def main():
    check_periods()
    t = change_second_head(cyclic_tail_negative(nested_negative_words()))
    assert periodic(t) == [599] + [0] * (N - 1)
    cases = (
        ("mod3", MOD3_MASKS, (293, 85, 56, 374784, 161, 85)),
        ("exact count", EXACT_MASKS, (333, 121, 56, 340480, 221, 121)),
        ("one additional mod3 trace", ORBIT_TRACE_MASKS, (317, 53, 64, 462336, 149, 61)),
    )
    for label, mask, metrics in cases:
        s = positive_words(t, mask)
        assert raw_stats(s, t) == metrics
        e = residual(s)
        check_transverse_trace(e)
        if label == "mod3":
            assert interior_failures(e) == (28, 48)
            check_peak56_gate(e)
        if label == "one additional mod3 trace":
            assert x_traces(e) == (False, True)
        print(label, "both transverse traces; raw mod16/exact/peak/SSE/mod32/mod64", metrics)


if __name__ == "__main__":
    main()
