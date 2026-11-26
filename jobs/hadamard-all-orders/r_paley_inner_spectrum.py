"""Verify a regular binary Gram factor with the prescribed Paley inner spectrum."""

from heapq import nlargest
from itertools import combinations
import json
from pathlib import Path

from verify import goethals_seidel, length_299_words, rows_from_columns, verify_orthogonal


def character_words(t):
    residues = sorted({x*x % t for x in range(1, t)})
    assert len(residues) == (t-1)//2 and t-1 not in residues
    squares = set(residues)

    def chi(x):
        x %= t
        return (1 if x in squares else -1) if x else 0

    d, f = [], []
    for x in residues:
        inverse = pow(x, -1, t)
        d.append([chi(1 + inverse*y) for y in residues])
        f.append([chi(1 - inverse*y) for y in residues])
    v = len(residues)
    assert all(f[i][i] == 0 and all(d[i]) for i in range(v))
    assert all(d[i][j] == d[j][i] and f[i][j] == -f[j][i] and f[i][j]
               for i, j in combinations(range(v), 2))
    for j in range(v):
        samples = tuple(zip(d[0], f[0], d[j], f[j], strict=True))
        assert sum(a*c + b*e for a, b, c, e in samples) == (
            t*(j == 0)-2
        )
        assert sum(a*e + b*c for a, b, c, e in samples) == 0
    return d, f


def verify_factor(t):
    d, f = character_words(t)
    v = len(d)
    h = 2*v
    mask = (1 << h) - 1
    positive = []
    for a, b in zip(f, d, strict=True):
        first = sum((x == 1) << j for j, x in enumerate(a))
        second = sum((x == 1) << j for j, x in enumerate(b))
        positive.append(first | (second << v))
    positive += [(a >> v) | ((a & ((1 << v) - 1)) << v) for a in positive]
    negative = [mask ^ a ^ (1 << i) for i, a in enumerate(positive)]
    first = [a | (b << h) for a, b in zip(positive, negative, strict=True)]
    second = [b | (a << h) for a, b in zip(positive, negative, strict=True)]
    rows = first + second
    assert all(a.bit_count() == t-2 for a in rows + rows_from_columns(2*h, rows))
    for i, j in combinations(range(2*h), 2):
        a, b = i % h, j % h
        same_half, same_group = i//h == j//h, a//v == b//v
        gram_b = h-2 + (a == b)
        gram_e = t*(a == b) - 2*same_group
        want = (gram_b + (gram_e if same_half else -gram_e))//2
        assert (rows[i] & rows[j]).bit_count() == want
    assert 2*h - (t-2) == t and t % 2 == 1
    assert h+2 == t+1 and h-2 == t-3
    return len(rows), len(rows)*(len(rows)-1)//2


def verify_sparse_bounds():
    t, m = 599, 1196
    source = goethals_seidel(length_299_words())
    assert verify_orthogonal(m, source) == 714610
    record = Path(__file__).with_name('r_paley_skew_inner_data.json')
    chosen = json.loads(record.read_text(encoding='ascii'))['w_columns']
    mask = (1 << m) - 1
    cases = (
        (range(t), t, (832, 2306), -148),
        (chosen, 0, (448, 1306, 2604, 4252), -82),
    )
    for w, gamma, expected, minimum in cases:
        w = set(w)
        assert len(w) == t and gamma not in w
        reserved = [mask ^ source[gamma] ^ col for j, col in enumerate(source)
                    if j not in w and j != gamma]
        assert len(reserved) == 596
        rows = rows_from_columns(m, reserved)
        minima = []
        scores = [[] for _ in expected]
        for i, a in enumerate(rows):
            corr = [len(reserved)-2*(a ^ b).bit_count() for j, b in enumerate(rows) if i != j]
            maxima = nlargest(2*len(expected), map(abs, corr))
            minima.append(min(corr))
            for j, values in enumerate(scores, 1):
                values.append(sum(maxima[:2*j]))
        observed = tuple(sum(nlargest(2*j+1, values)) for j, values in enumerate(scores, 1))
        assert observed == expected
        assert all(u < 2*j*(t+1) for j, u in enumerate(observed, 1))
        assert min(minima) == minimum and 4*len(reserved) + 12*minimum > 0
        print(f'Paley inner source gamma={gamma}: sparse bounds {observed}, minimum V product {minimum}')


if __name__ == '__main__':
    assert verify_factor(7) == (12, 66)
    size, pairs = verify_factor(599)
    assert (size, pairs) == (1196, 714610)
    print(f'Paley inner sign-square: size {size}, all {pairs} Gram pairs, spectrum 4^600 and 2396^596')
    verify_sparse_bounds()
