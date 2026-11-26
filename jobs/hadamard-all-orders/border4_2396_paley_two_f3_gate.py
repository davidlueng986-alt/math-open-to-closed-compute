"""Exact verification of local amplitude conditions for either complementary F3 pair."""

from collections import Counter
from itertools import product

from border4_2396_dual_mod5_forest import forest, reciprocal
from border4_2396_paley_negative_norm import N, sign_word
from border4_2396_paley_peak32_gates import FACTORS_3, anchored_residual, check_factors_3, kernel
from border4_2396_paley_relative_trace_gate import PROJECTED_TRACE_LAGS, inverse_class
from border4_2396_paley_reselected_heads import FIXTURES
from border4_2396_primitive_field import remainder

CERTIFICATES = (
    ((0, 2), (2, 0, 1, 1),
     (2, 16, 28, 29, 30, 31, 34, 37, 55, 95, 109, 121),
     (3, 9, 12, 17, 18, 19, 26, 38, 39, 46, 49, 52, 54, 57, 60, 64, 72, 74, 79, 80,
      81, 83, 86, 87, 88, 90, 97, 99, 100, 101, 105, 107, 115, 117, 120, 126, 128, 129,
      130, 132, 133, 134, 135, 142, 143, 146, 147, 148),
     (3, 7, 10, 22, 23, 25, 48)),
    ((1, 3), (2, 1, 1, 1),
     (4, 6, 8, 9, 15, 16, 28, 40, 57, 76, 78, 109, 113),
     (3, 17, 18, 26, 34, 38, 39, 49, 51, 52, 54, 55, 58, 60, 64, 72, 79, 80, 81, 83,
      86, 87, 88, 90, 92, 97, 99, 100, 101, 105, 107, 115, 117, 120, 126, 128, 129, 130,
      132, 133, 135, 142, 143, 146, 147, 148),
     (3, 7, 10, 11, 16, 22, 23, 48)),
)


def columns_for_cubic(cubic):
    a = [(1, 0, 0)]
    for _ in range(13):
        a.append(remainder((0,) + a[-1], cubic, 3))
    assert a.pop() == a[0] and len(set(a)) == 13
    return tuple((1, *a[x], *a[-x]) for x in range(13))


def check_assignment(cubic, pairs):
    matched = Counter()
    cubics = (cubic, reciprocal(cubic, 3))
    for i in pairs:
        p = FACTORS_3[i]
        for q in (p, reciprocal(p, 3)):
            values = []
            for k, t in enumerate(cubics):
                exponents = {92*j % N: c for j, c in enumerate(t)}
                evaluated = tuple(exponents.get(j, 0) for j in range(N))
                if not any(remainder(evaluated, q, 3)):
                    values.append(k)
            assert len(values) == 1
            matched[values[0]] += 1
    assert matched == {0: 2, 1: 2}


def prove_columns(e, cubic, zeros, boxes):
    basis = kernel(columns_for_cubic(cubic), 3)
    assert len(basis) == 6
    codewords = tuple(tuple(sum(c*b[i] for c, b in zip(coeff, basis, strict=True)) % 3
                            for i in range(13))
                      for coeff in product(range(3), repeat=6))
    zero = (0,)*7
    totals = {zero: 1}
    for y in range(12):
        lags = tuple(inverse_class(92*x+208*y, N) for x in range(13))
        local = Counter()
        for word in codewords:
            if not y and any(word[x] != word[-x] for x in range(13)):
                continue
            if any(value and (not e[d] or d in zeros or (d in boxes and value != e[d] % 3))
                   for value, d in zip(word, lags, strict=True)):
                continue
            part = tuple((word[x]+(word[-x] if y else 0)) % 3 for x in range(7))
            local[part] += 1
        combined = {}
        for u, a in totals.items():
            for v, b in local.items():
                dest = tuple((c+d) % 3 for c, d in zip(u, v, strict=True))
                combined[dest] = min(2, combined.get(dest, 0)+a*b)
        totals = combined
    assert totals[zero] == 1


def main():
    check_factors_3()
    e = anchored_residual(tuple(map(sign_word, FIXTURES[1][0])))
    assert sum(not r for r in e[1:]) == 29
    original_high = {d for d in range(1, 150) if abs(e[d]) >= 3}
    for pairs, cubic, zeros, boxes, orbits in CERTIFICATES:
        assert all(e[d] for d in zeros) and all(abs(e[d]) == 1 for d in boxes)
        check_assignment(cubic, pairs)
        prove_columns(e, cubic, set(zeros), set(boxes))
        high = original_high.difference(zeros)
        remove = set()
        for rep in orbits:
            d = dict(PROJECTED_TRACE_LAGS)[rep]
            orbit = {inverse_class(rep*m, N) for m in (1, 139, 185)}
            assert orbit.intersection(high) == {d}
            remove.add(d)
        assert not forest(sorted(high-remove))[1]
        print(f"Primitive F3 pairs {pairs}: {len(zeros)} extra zeros, {len(boxes)} small boxes, "
              f"{len(orbits)} selected orbit parities complete the bounded-lag gate")


if __name__ == "__main__":
    main()
