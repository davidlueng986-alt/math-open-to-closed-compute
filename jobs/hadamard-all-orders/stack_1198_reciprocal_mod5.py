"""Verify reciprocal mod-five support and small-residual rematching controls."""
from collections import Counter, defaultdict
import json
from pathlib import Path

from stack_1197 import LOWER_FLIPS, LOWER_OMITTED, UPPER_FLIPS, flipped_column, source_matrices
from stack_1198_channels import signatures
from stack_1198_joint import signature
from stack_1198_mod5 import Basis, bit_sign
from stack_1198_reciprocal import reciprocal_channels
from verify import paley


def pairing(words):
    upper, base = source_matrices()
    n, m = len(upper), len(base)
    u = flipped_column(n, UPPER_FLIPS)
    v = flipped_column(m, LOWER_FLIPS)
    x = upper[words['upper_pivot']] ^ sum(1 << i for i in words['upper_flips'])
    lower, y = reciprocal_channels(base, v, words)
    a, sig_a = signatures(upper, u, x)
    b, sig_b = signatures(lower, v, y)
    supply = defaultdict(list)
    for i, key in enumerate(sig_a):
        supply[key].append(i)
    pairs = {}
    for j in range(m // 2):
        if j not in LOWER_OMITTED:
            pairs[supply[sig_b[j]].pop()] = j
    left, right = defaultdict(list), defaultdict(list)
    for (first, second), indices in supply.items():
        for i in indices:
            left[first].append((second, i))
    for j in range(m // 2, m):
        if j not in LOWER_OMITTED:
            first, second = sig_b[j]
            right[first].append((second, j))
    for first, entries in left.items():
        for (_, i), (_, j) in zip(sorted(entries), sorted(right[first]), strict=True):
            pairs[i] = j
    assert set(pairs) == set(range(n))
    residues = [0] * m
    for i, j in pairs.items():
        a1, a2 = a[i]
        b1, b2 = b[j]
        align = -1 if (a1 or a2) * (b1 or b2) > 0 else 1
        assert a1 + align * b1 == 0
        residues[j] = align * a2 + b2
    retained = [pair for j, pair in enumerate(b) if j not in LOWER_OMITTED]
    top_mod = Counter(signature(*pair, 20) for pair in a)
    lower_mod = Counter(signature(*pair, 20) for pair in retained)
    assert sum(second**2 for _, second in a) == sum(second**2 for _, second in retained)
    assert sum(first * second for first, second in a) == sum(first * second for first, second in retained)
    return sig_b, residues, sum((top_mod - lower_mod).values())


def verify_reciprocal(words):
    sig_b, residuals, deficit = pairing(words)
    energy = sum(value**2 for value in residuals)
    assert not any(residuals[:600]) and energy == 1888
    paley_columns = paley(599)
    support = [j for j in range(600) if residuals[600 + j]]
    basis = Basis(600)
    for j in support:
        assert basis.add([bit_sign(paley_columns[j], i) for i in range(600)])
    assert basis.rank == 115
    omitted = {j - 600 for j in LOWER_OMITTED if j >= 600}
    available = set(range(600)) - set(support) - omitted
    counts = Counter(sig_b[600:])
    chosen = set(support)
    for j in sorted(available, key=lambda i: (counts[sig_b[i + 600]], i)):
        if basis.add([bit_sign(paley_columns[j], i) for i in range(600)]):
            chosen.add(j)
        if basis.rank == 300:
            break
    assert len(chosen) == basis.rank == 300
    protected = set(range(600)) - chosen - omitted
    assert len(protected) == 299 and not protected.intersection(support)
    syndrome = [sum(residuals[j + 600] // 4 * bit_sign(paley_columns[j], i) for j in support)
                for i in range(600)]
    assert sum(value**2 for value in syndrome) == 600 * energy // 16
    assert sum(value % 5 != 0 for value in syndrome) == 472
    assert sum(value % 25 != 0 for value in syndrome) == 555
    assert deficit == 50
    print('reciprocal mod5 support: rank 115 extended to 300; 896 exact anchors; 50 signed mod20 mismatches')


def control(slots, p):
    first, upper, lower = zip(*slots, strict=True)
    residuals = [a - b for a, b in zip(upper, lower, strict=True)]
    step = 4 * p
    assert p % 2 and all(a % 4 == 0 for a in (*upper, *lower))
    assert all(value % step == 0 for value in residuals)
    assert sum(a**2 for a in upper) == sum(b**2 for b in lower)
    assert sum(t * value for t, value in zip(first, residuals, strict=True)) == 0
    top_deck = Counter(signature(t, a) for t, a in zip(first, upper, strict=True))
    lower_deck = Counter(signature(t, b) for t, b in zip(first, lower, strict=True))
    return sum(value**2 for value in residuals), top_deck == lower_deck


def verify_controls():
    assert control(((4, 20, 0), (4, 0, 20)), 5) == (800, True)
    assert control(((0, 8, -4), (0, 4, -8)), 3) == (288, True)
    assert control(((4, 0, 20), (4, 0, 20), (4, 0, -20), (4, 40, 20)), 5) == (1600, False)
    assert control(((0, 20, -20),), 5) == (1600, True)
    print('low-energy rematching: positive and first-zero swaps; sharp abstract threshold 1600')


def main():
    path = Path(__file__).with_name('stack_1198_reciprocal_data.json')
    words = json.loads(path.read_text(encoding='ascii'))['radius34']
    verify_reciprocal(words)
    verify_controls()


if __name__ == '__main__':
    main()
