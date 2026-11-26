"""Replay shared ternary information sets and the integer finish on the physical anchors."""

from border4_2396_paley_negative_norm import periodic, sign_word
from border4_2396_paley_peak32_gates import FACTORS_3, column, kernel
from border4_2396_paley_projected_f3 import ORBITS, exact_pairs, relabel
from border4_2396_paley_two_f3 import FIXTURES, HEADS

LAGS = range(1, 150)


def inverse_class(lag, modulus):
    return min(lag % modulus, -lag % modulus)


def residual(u, v, tail, multiplier):
    w = sign_word(tail)
    e = periodic((u, v, w, w))
    e[0] -= 1196
    assert all(x % 8 == 0 for x in e)
    assert all(sum(e[i::q]) == 0 for q in (13, 23) for i in range(q))
    return relabel(tuple(e), multiplier)


def coordinate_pivot(value, basis):
    for i, row in basis.items():
        scale = value[i]
        if scale:
            value = tuple((a-scale*b) % 3 for a, b in zip(value, row, strict=True))
    lead = next((i for i, x in enumerate(value) if x), None)
    if lead is None:
        return None
    return lead, tuple(x * value[lead] % 3 for x in value)


def shared_information_set(e, pairs):
    triples = tuple(tuple(sorted((*pairs, i))) for i in range(4) if i not in pairs)
    matrices = tuple(tuple(column(d, tuple(FACTORS_3[i] for i in t), 3) for d in LAGS)
                     for t in triples)
    forms = tuple(tuple(zip(*kernel(matrix, 3), strict=True)) for matrix in matrices)
    assert all(len(coordinates[0]) == 32 for coordinates in forms)
    bases = ({}, {})
    chosen = []
    available = sorted((d for d in LAGS if e[d] % 24 == 0), key=lambda d: (abs(e[d]), d))
    for d in available:
        pivots = tuple(coordinate_pivot(f[d-1], b) for f, b in zip(forms, bases, strict=True))
        if None not in pivots:
            chosen.append(d)
            for b, (lead, row) in zip(bases, pivots, strict=True):
                b[lead] = row
    assert len(chosen) == 32
    for mat in matrices:
        assert not kernel(tuple(mat[d-1] for d in LAGS if d not in chosen), 3)
    return tuple(chosen)


def quotient_column(d):
    return (1 << inverse_class(d, 13)) ^ (1 << (7 + inverse_class(d, 23)))


def dependent_columns(lags, columns, residual):
    basis = {}
    checks = []
    for d in sorted(lags, key=lambda d: (-abs(residual[d]), d)):
        value = columns[d]
        while value.bit_length() in basis:
            value ^= basis[value.bit_length()]
        if value:
            basis[value.bit_length()] = value
        else:
            checks.append(d)
    return tuple(checks)


def integer_finish(e):
    orbit_lags = tuple({inverse_class(d*m, 299) for m in (1, 139, 185)} for d in ORBITS)
    assert all(sum(e[d] for d in lags) % 16 == 0 for lags in orbit_lags)
    assert max(map(abs, e)) < 72
    quotient = {d: quotient_column(d) for d in LAGS}
    augmented = {d: c ^ sum(1 << (19+j) for j, lags in enumerate(orbit_lags) if d in lags)
                 for d, c in quotient.items()}
    odd = tuple(d for d in LAGS if abs(e[d]) >= 24 and e[d] % 16)
    even = tuple(d for d in LAGS if abs(e[d]) >= 48 and e[d] % 32)
    return dependent_columns(odd, augmented, e), dependent_columns(even, quotient, e)


def main():
    u, v = map(sign_word, HEADS[2][0][:2])
    exact = (16, 20, 14, 15, 13)
    for i, (_, pairs, multiplier, tail, _, _) in enumerate(FIXTURES):
        e = residual(u, v, tail, multiplier)
        assert exact_pairs(e) == pairs
        chosen = shared_information_set(e, pairs)
        count = sum(e[d] == 0 for d in chosen)
        assert count == exact[i]
        print(f"{pairs} m={multiplier}: shared ternary information set {len(chosen)}, "
              f"integer zeros {count}, lags {chosen}")
        if i in (3, 4):
            checks = integer_finish(e)
            assert tuple(map(len, checks)) == {3: (19, 8), 4: (18, 4)}[i]
            print(f"additional mod-16 and mod-32 integer finish: {checks}")


if __name__ == '__main__':
    main()
