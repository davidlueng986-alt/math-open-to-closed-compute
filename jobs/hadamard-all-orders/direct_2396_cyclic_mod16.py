"""Reconstruct a same-word direct modulo-sixteen fixture by phase elimination."""

import json
from pathlib import Path

from direct_2396_cyclic import quarter_correlations
from direct_2396_cyclic_ap import P, HALF, SIZES, construct_first_pair, reflection, rotation, word


DATA = Path(__file__).with_name("direct_2396_cyclic_mod16_data.json")
FOLD = (1 << (HALF+1)) - 2


def binary_word(word_text):
    assert len(word_text) == P and set(word_text) <= {'+', '-'}
    return sum((code == '-') << i for i, code in enumerate(word_text))


def residue(words):
    return quarter_correlations(tuple(map(word, words)))[1:]


def half_parity(values):
    assert not any(x % 2 for x in values)
    return sum((values[d-1]//2 & 1) << d for d in range(1, HALF+1))


def column(disagreement, d):
    mixed = rotation(disagreement, d) ^ rotation(disagreement, -d)
    squared = (1 << (2*d % P)) | (1 << ((-2*d) % P))
    edge_at_anchor = ((1 << d) | (1 << (P-d))) if not disagreement >> d & 1 else 0
    return (mixed ^ squared ^ edge_at_anchor) & FOLD


def solve(columns, rhs):
    basis = {}
    kernel = []
    for d, direction in enumerate(columns, 1):
        selection = 1 << d
        while direction:
            j = direction.bit_length()-1
            if j not in basis:
                basis[j] = direction, selection
                break
            vector, chosen = basis[j]
            direction ^= vector
            selection ^= chosen
        else:
            kernel.append(selection)
    selected = 0
    while rhs:
        vector, chosen = basis[rhs.bit_length()-1]
        rhs ^= vector
        selected ^= chosen
    return selected, kernel


def solve_fixture():
    c, d = map(binary_word, json.loads(DATA.read_text()))
    assert not d & ~c and (c.bit_count(), d.bit_count()) == SIZES[2:]
    a, b = construct_first_pair(P, c ^ d, d, 0)
    shapes = (a, b, c, d)
    base = half_parity(residue(shapes))
    disagreement = b ^ reflection(b)
    columns = [column(disagreement, j) for j in range(1, HALF+1)]

    choices = (1 << 1) | (1 << 77) | (1 << 138) | (1 << 258)
    mask = choices | reflection(choices)
    expected = columns[0] ^ columns[76] ^ columns[137] ^ columns[257]
    assert half_parity(residue((a ^ mask, b ^ mask, c, d))) ^ base == expected
    selected, kernel = solve(columns, base)
    assert len(kernel) == 2
    affine = [selected]
    for direction in kernel:
        affine += [x ^ direction for x in affine]
    allowed = []
    for chosen in affine:
        flip = chosen | reflection(chosen)
        candidate = a ^ flip, b ^ flip, c, d
        residual = residue(candidate)
        assert not any(x % 4 for x in residual)
        if tuple(x.bit_count() for x in candidate) == SIZES:
            allowed.append((sum(x*x for x in residual), residual))
    assert allowed
    square, residual = min(allowed)
    assert square == 151168
    assert sum(x != 0 for x in residual) == 532 and max(map(abs, residual)) == 40
    assert any(x % 3 for x in residual) and any(x % 11 for x in residual)
    assert pow(11, 598, P) == 1
    assert all(pow(11, 598//q, P) != 1 for q in (2, 13, 23))
    print("Direct cyclic: full raw mod16, exact sums (1,3,19,45), peak160, 532 nonzero shifts.")


if __name__ == "__main__":
    solve_fixture()
