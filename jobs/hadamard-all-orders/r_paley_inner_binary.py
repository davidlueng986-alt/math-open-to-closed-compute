"""Check the binary criterion for modular compatibility of Paley inner columns."""

from itertools import combinations
import json
from pathlib import Path

from r_paley_anchored_triples import COSELECTED_SINGLES, COSELECTED_W, mixed_columns
from r_paley_projective_lift import build
from stack_1198_joint import dot
from verify import goethals_seidel, length_299_words


def odd(value):
    return value.bit_count() % 2


def binary_dot(left, right):
    return odd(left & right)


def extend(width, selected):
    """Complete a binary orthonormal family when the complement is nonalternating."""
    canonical = (1 << width) - 1
    for vector in selected:
        canonical ^= vector
    if not canonical:
        return selected if len(selected) == width else None
    basis = {}
    for i in range(width):
        vector = 1 << i
        for q in selected:
            if q >> i & 1:
                vector ^= q
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = vector
                break
            vector ^= basis[pivot]
    complement = list(basis.values())
    assert len(complement) == width-len(selected)
    finished = list(selected)
    while complement:
        slot = next(i for i, v in enumerate(complement) if odd(v))
        new = complement.pop(slot)
        if new == canonical and complement:
            # The other basis words can all be taken even in this case.
            # Adding one of them changes the chosen norm-one vector while
            # leaving a basis of the same old complement.
            even = next((q for q in complement if not odd(q)), None)
            if even is not None:
                new ^= even
            else:
                alternative = complement.pop()
                complement.append(new)
                new = alternative
        assert odd(new)
        finished.append(new)
        canonical ^= new
        complement = [v ^ (new if binary_dot(v, new) else 0) for v in complement]
        assert bool(canonical) == bool(complement)
    return finished


def verify():
    t = 599
    m = 2*t-2
    mask = (1 << m) - 1
    path = Path(__file__).with_name('r_paley_skew_inner_data.json')
    data = json.loads(path.read_text(encoding='ascii'))
    source = goethals_seidel(length_299_words())
    w_indices = data['w_columns']
    flips = list(zip(data['inner_rows'], data['inner_columns'], strict=True))
    _, inside = build(t, source, flips, w_indices, gamma_index=0)
    d = 0
    for i in w_indices:
        # In the normalized source the negative support is col XOR gamma.
        d ^= source[i] ^ source[0]
    assert not odd(d)
    witnesses = inside[2:]
    vectors = tuple(((col >> (2*t)) & mask) ^ d for col in witnesses)
    assert all(odd(v) for v in vectors)
    assert all(not binary_dot(v, w) for v,w in combinations(vectors,2))
    assert ((1 << m)-1) != reduce_xor(vectors)

    # Include individually compatible but mutually incompatible samples.
    extra = []
    excluded = set(w_indices) | {0}
    for g,col in enumerate(source):
        if g in excluded:
            continue
        normalized = mask ^ source[0] ^ col
        r = (normalized & -normalized).bit_length()-1
        extra.append((r,g))
        if len(extra) == 16:
            break
    _, inside = build(t, source, [*flips,*extra], w_indices, gamma_index=0)
    test = inside[2:]
    binary = [((col >> (2*t)) & mask) ^ d for col in test]
    assert all((dot(4*t,col,other) % 8) == 4*binary_dot(x,y)
               for (col,x),(other,y) in combinations(zip(test,binary,strict=True),2))
    assert any(binary_dot(x,y) for x,y in combinations(binary,2))

    assert extend(3,(7,)) is None  # odd seed spanning the canonical vector
    full = extend(m,vectors)
    assert len(full) == m and all(odd(q) for q in full)
    assert all(not binary_dot(x,y) for x,y in combinations(full,2))
    print('Paley inner candidates: extracted 11 binary columns, exact modulo-eight pair criterion')

    selected = tuple(i for i in range(m) if COSELECTED_W >> i & 1)
    mixed_flips = [(g, (r,)) for r, g in COSELECTED_SINGLES]
    mixed_flips.append((376, (868, 1046, 1071)))
    mixed = mixed_columns(t, source, selected, 0, mixed_flips)[-len(mixed_flips):]
    d = reduce_xor(source[i] ^ source[0] for i in selected)
    assert not odd(d)
    vectors = tuple(((col >> (2*t)) & mask) ^ d for col in mixed)
    full = extend(m, vectors)
    assert len(full) == m and all(odd(q) for q in full)
    assert all(not binary_dot(x,y) for x,y in combinations(full,2))
    print('Paley inner parity: full 1196-column binary bases extending 1211 and 1212 witnesses')


def reduce_xor(values):
    total = 0
    for value in values:
        total ^= value
    return total


if __name__ == '__main__':
    verify()
