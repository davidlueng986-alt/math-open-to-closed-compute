"""Replay a heterogeneous-modulus valuation forest on a physical word."""

from itertools import product
from math import log2

from border4_2396 import periodic
from border4_2396_adaptive_forest import EDGES, forest, lags
from border4_2396_dual_changed_support import cyclic_tail_negative, positive_words
from border4_2396_dual_joint_geometry import change_second_head, raw_stats
from border4_2396_dual_mod5_forest import residual
from border4_2396_nested import nested_negative_words
from border4_2396_primitive_traces import MOD3_MASKS, check_transverse_trace

# Moduli in folded edge order, with 10 through 13 written in base 16.
DIFFERENCE = (
    "1111111111117353931515113353b53d13d131111533357155313313d551115335b5373155379d33513"
)
SUM = (
    "14481211323153143325134123311541331163323333443137524646144116443519333131115153534"
)


def valuation(w):
    positive = abs(w)
    assert positive
    return (positive & -positive).bit_length() - 1


def permitted_weights(caps, difference, total):
    if len(caps) == 1:
        assert difference == 1
        return range(total, caps[0] + 1, total)
    A, B = caps
    assert difference % 2 == 1 and difference > min(A, B)
    return {a + b for a, b in product(range(-A, A + 1), range(-B, B + 1))
            if (a - b) % difference == 0 and a + b > 0 and (a + b) % total == 0}


def check_gate(e, bounds, difference, total):
    """Return forest sizes and failed congruence counts for given local bounds."""
    assert all(abs(x) <= b for x, b in zip(e, bounds, strict=True))
    assert e[0] == 0 and tuple(e[1:]) == tuple(reversed(e[1:]))
    assert all(sum(e[i::q]) == 0 for q in (13, 23) for i in range(q))
    layers = {}
    failed_difference = failed_sum = 0
    for edge, d, s in zip(EDGES, difference, total, strict=True):
        shifts = lags(edge)
        a = tuple(e[i] for i in shifts)
        caps = tuple(bounds[i] for i in shifts)
        failed_difference += (a[0] - a[-1]) % d != 0
        failed_sum += sum(a) % s != 0
        for level in {valuation(w) for w in permitted_weights(caps, d, s)}:
            layers.setdefault(level, set()).add(edge)
    assert all(len(forest(sorted(edges))) == len(edges) for edges in layers.values())
    if failed_difference == failed_sum == 0:
        assert not any(e)
    return tuple(len(edges) for _, edges in sorted(layers.items())), failed_difference, failed_sum


def main():
    negative = change_second_head(cyclic_tail_negative(nested_negative_words()))
    assert periodic(negative) == [599] + [0] * 298
    positive = positive_words(negative, MOD3_MASKS)
    assert raw_stats(positive, negative) == (293, 85, 56, 374784, 161, 85)
    e = residual(positive)
    check_transverse_trace(e)
    difference = tuple(int(c, 16) for c in DIFFERENCE)
    total = tuple(int(c, 16) for c in SUM)
    result = check_gate(e, tuple(map(abs, e)), difference, total)
    assert result == ((17, 17, 16, 6), 26, 18)
    bits = sum(log2(a * b) for a, b in zip(difference, total, strict=True))
    assert round(bits, 5) == 228.31839
    print("valuation forests", result[0], "failed difference/sum", result[1:],
          "log2 alphabet product", round(bits, 5))


if __name__ == "__main__":
    main()
