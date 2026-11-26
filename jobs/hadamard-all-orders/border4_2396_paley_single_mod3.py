"""Check a one-factor mod-3 closure gate for the reselected Paley head."""

from itertools import product

from border4_2396_paley_negative_norm import N, sign_word
from border4_2396_paley_peak32_gates import (
    FACTORS_3, anchored_residual, check_factors_3, column, inverse, interval, kernel, subtract,
)
from border4_2396_paley_reselected_heads import FIXTURES


def independent_coordinates(forms, choices, dimension):
    pivots = {}
    indices = []
    for i in sorted(range(len(forms)), key=lambda i: (len(choices[i]), i)):
        form = list(forms[i])
        for p, pivot in sorted(pivots.items()):
            if form[p]:
                form = subtract(form, pivot, form[p], 3)
        lead = next((p for p, c in enumerate(form) if c), None)
        if lead is not None:
            scale = pow(form[lead], -1, 3)
            pivots[lead] = tuple(scale*c % 3 for c in form)
            indices.append(i)
            if len(indices) == dimension:
                return indices
    raise AssertionError("missing independent coordinates")


def audit_factor(e, index):
    support = tuple(d for d in range(1, 150) if abs(e[d]) >= 2)
    choices = tuple(tuple(interval((abs(e[d])//2) * (1 if e[d] > 0 else -1))) for d in support)
    basis = kernel(tuple(column(d, (FACTORS_3[index],), 3) for d in support), 3)
    dim = len(basis)
    assert dim == 17
    forms = tuple(zip(*basis, strict=True))
    positions = independent_coordinates(forms, choices, dim)
    transform = inverse(tuple(forms[i] for i in positions), 3)
    remain = sorted(set(range(len(forms))).difference(positions), key=lambda i: (len(choices[i]), i))
    checks = []
    for i in remain:
        row = tuple(sum(a*transform[k][j] for k, a in enumerate(forms[i])) % 3 for j in range(dim))
        allowed = {value % 3: value for value in choices[i]}
        assert len(allowed) == len(choices[i])
        checks.append((i, row, allowed))

    trials = boxed = complete = 0
    for coordinates in product(*(choices[i] for i in positions)):
        trials += 1
        entries = []
        for i, row, allowed in checks:
            residue = sum(a*b for a, b in zip(row, coordinates, strict=True)) % 3
            if residue not in allowed:
                break
            entries.append(allowed[residue])
        else:
            boxed += 1
            values = [0]*N
            for i, val in zip(positions + remain, (*coordinates, *entries), strict=True):
                d = support[i]
                values[d] = values[-d] = val
            if all(sum(values[j::q]) == 0 for q in (13, 23) for j in range(q)):
                assert not any(values)
                complete += 1
    assert (trials, boxed, complete) == (131072, 3 if index == 1 else 1, 1)
    print(f"Primitive mod-3 factor {index}: {trials} combinations, {boxed} in the intervals, only zero exact-dual")


def main():
    check_factors_3()
    e = anchored_residual(tuple(map(sign_word, FIXTURES[0][0])))
    for i in range(4):
        audit_factor(e, i)


if __name__ == "__main__":
    main()
