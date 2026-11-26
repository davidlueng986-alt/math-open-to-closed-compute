"""Check the modulo-three reflection lift and a fixed-tail parity screen."""

import json
from pathlib import Path

from direct_2396_cyclic import quarter_correlations
from direct_2396_cyclic_ap import P, HALF, reflection, rotation
from verify import goethals_seidel, signs, verify_orthogonal


DATA = Path(__file__).with_name("direct_2396_cyclic_mod12_data.json")
PAIR_MASK = (1 << (HALF+1)) - 2


def divide_by_pair(values):
    """Solve (z+z^-1) times a word in F3[C599]."""
    shifted = [values[(i-1) % P] % 3 for i in range(P)]
    value = 0
    for j in range(1, P):
        value = (shifted[2*j % P]-value) % 3
    result = [0] * P
    result[0] = 2*(shifted[0]-value) % 3
    for j in range(1, P):
        i = 2*j % P
        result[i] = (shifted[i]-result[(i-2) % P]) % 3
    assert all((result[(i-1) % P]+result[(i+1) % P]-values[i]) % 3 == 0
               for i in range(P))
    return result


def parity_rank_and_membership(disagreement, target):
    basis = {}
    for i in range(1, HALF+1):
        if not disagreement >> i & 1:
            continue
        column = rotation(disagreement, i) ^ rotation(disagreement, -i)
        column ^= (1 << (2*i % P)) | (1 << (-2*i % P))
        column &= PAIR_MASK
        while column:
            k = column.bit_length()-1
            if k not in basis:
                basis[k] = column
                break
            column ^= basis[k]
    while target:
        k = target.bit_length()-1
        if k not in basis:
            return len(basis), False
        target ^= basis[k]
    return len(basis), True


def check_witness():
    v, d = json.loads(DATA.read_text())
    assert len(v) == len(d) == P
    assert set(v) <= {'+', '-', '.'} and set(d) <= {'+', '-'}
    assert [i for i, x in enumerate(v) if x == '.'] == [1, P-1]
    negative = sum((x == '-') << i for i, x in enumerate(d))
    target = [-(P-2*(negative ^ rotation(negative, lag)).bit_count()) for lag in range(P)]
    target[0] += 4*P
    traces = divide_by_pair(target)
    ternary = [1 if x == '+' else -1 if x == '-' else 0 for x in v]
    assert all((ternary[i]+ternary[-i % P]-traces[i]) % 3 == 0 for i in range(P))
    a, b = v.replace('.', '-'), v.replace('.', '+')
    words = (a, b, b, d)
    assert tuple(sum(signs(w)) for w in words) == (17, 21, 21, 35)
    error = quarter_correlations(words)[1:]
    assert all(x % 3 == 0 for x in error)
    peak, energy = 4*max(map(abs, error)), 16*sum(x*x for x in error)
    assert (peak, energy, sum(x != 0 for x in error)) == (108, 1519488, 554)
    assert any(x % 11 for x in error)
    assert pow(2, 299, P) == 1 and all(pow(2, k, P) != 1 for k in (13, 23))
    early = sum((x == '-') << i for i, x in enumerate(v))
    disagreement = early ^ reflection(early)
    bits = sum((error[j-1] & 1) << j for j in range(1, HALF+1))
    possible = (disagreement & PAIR_MASK).bit_count()
    rank, solvable = parity_rank_and_membership(disagreement, bits)
    assert rank == possible-1 and not solvable
    print(f"Direct ternary reflection: all 598 raw mod12, peak {peak}, "
          f"{possible} free reflected pairs, rank {rank}, no additional mod8 lift for this tail.")


def check_small_controls():
    for words in (("+-+--+-", "+++--++", "+++--++", "+++-++-"),
                  ("+-+-++---+-", "+++-++---++", "+++-++---++", "++++-++-++-")):
        n = len(words[0])
        assert [i for i, (a, b) in enumerate(zip(words[0], words[1], strict=True))
                if a != b] == [1, n-1]
        assert words[1] == words[2]
        assert not any(quarter_correlations(words)[1:])
        assert verify_orthogonal(4*n, goethals_seidel(tuple(map(signs, words)))) == 2*n*(4*n-1)
    print("Order 28 and 44: exact controls with a repeated word and a two-bit partner.")


if __name__ == "__main__":
    check_witness()
    check_small_controls()
