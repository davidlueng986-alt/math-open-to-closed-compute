"""Exact controls for uniform and tensor-source Paley inner growth."""

from collections import Counter, defaultdict
from itertools import combinations

from r_paley_projective_lift import build
from verify import paley, verify_orthogonal


SKEW_FOUR = (
    (1, 1, 1, 1),
    (-1, 1, 1, -1),
    (-1, -1, 1, 1),
    (-1, 1, -1, 1),
)


def sign(word, row):
    return 2 * (word >> row & 1) - 1


def pattern(values):
    return sum((value != values[0]) << i for i, value in enumerate(values[1:]))


def buckets(source, rows):
    table = defaultdict(list)
    for j, word in enumerate(source):
        table[pattern([sign(word, r) for r in rows])].append(j)
    return table


def assemble(t, source, rows, reserve, selected):
    m = 2*t-2
    k = len(rows)
    assert len(source) == m and verify_orthogonal(m, source) == m*(m-1)//2
    assert len(set(rows)) == k and len(selected) == t+1 and len(reserve) == k
    assert len(set(reserve + selected)) == k+t+1
    for i, j in combinations(range(k), 2):
        a, b = rows[i], rows[j]
        actual = sum(sign(source[c], a)*sign(source[c], b) for c in selected)
        g, h = source[reserve[i]], source[reserve[j]]
        target = sign(g, a)*sign(g, b) + sign(h, b)*sign(h, a)
        assert actual == target

    gamma, *w = selected
    oriented = list(source)
    for row, j in zip(rows, reserve, strict=True):
        if sign(source[j], row) != sign(source[gamma], row):
            oriented[j] ^= (1 << m)-1
    outside, inside = build(t, oriented, zip(rows, reserve, strict=True), w, gamma)
    columns = outside + inside
    assert len(inside) == k+2 and len(columns) == 2*t+2+k
    pairs = verify_orthogonal(4*t, columns)
    assert pairs == len(columns)*(len(columns)-1)//2
    return len(columns), pairs


def select_columns(table, reserve_patterns, counts):
    reserve = [table[p].pop() for p in reserve_patterns]
    assert all(len(table[p]) >= n >= 0 for p, n in counts.items())
    selected = [j for p, n in sorted(counts.items()) for j in table[p][:n]]
    return reserve, selected


def four_control(t):
    source = paley(2*t-3)
    rows = [0, 1, 2, 3]
    if t % 4 == 1:
        rows[3] = next(r for r in range(3, len(source))
                       if len({sign(c, 0)*sign(c, 1)*sign(c, 2)*sign(c, r) for c in source}) == 2)
    table = buckets(source, rows)
    even, odd = len(table[0]), len(table[1])
    if (even > odd) == (t % 4 == 3):
        source = [c ^ (1 << rows[-1]) for c in source]
        table = buckets(source, rows)
        even, odd = odd, even
    assert even + odd == (t-1)//2
    assert all(len(table[p]) == (odd if p.bit_count() % 2 else even) for p in range(8))
    if t % 4 == 3:
        reserve_matrix = SKEW_FOUR
        n = (t+1)//4
        x = max(0, n-(odd-1))
        counts = {p: (n-x if p.bit_count() % 2 else x) for p in range(8)}
    else:
        reserve_matrix = tuple(tuple(1 if i == j else -1 for j in range(4)) for i in range(4))
        n = (t-5)//4
        x = max(0, n-(odd-1))
        counts = {p: (n-x if p.bit_count() % 2 else x+2*(p != 0)) for p in range(8)}
    reserve_patterns = [pattern(list(c)) for c in zip(*reserve_matrix, strict=True)]
    reserve, selected = select_columns(table, reserve_patterns, counts)
    return assemble(t, source, rows, reserve, selected)


def sylvester(m):
    return [sum(((i & j).bit_count() % 2 == 0) << i for i in range(m)) for j in range(m)]


def double(source):
    m = len(source)
    mask = (1 << m)-1
    return [c | (c << m) for c in source] + [c | ((c ^ mask) << m) for c in source]


def cosets(k):
    h = 1 << (k-1).bit_length()
    linear = {pattern([1-2*((i & j).bit_count() % 2) for i in range(k)]) for j in range(h)}
    assert len(linear) == h
    unused = set(range(1 << (k-1)))
    result = []
    while unused:
        offset = min(unused)
        part = tuple(sorted(offset ^ p for p in linear))
        assert set(part) <= unused
        result.append(part)
        unused.difference_update(part)
    return result


def coset_control(t, source, rows, reserve_shift, remainder_shift):
    k, m = len(rows), len(source)
    table = buckets(source, rows)
    partitions = cosets(k)
    h = len(partitions[0])
    size = 1 << (k-1)
    assert sum((size*len(table[p])-m)**2 for p in range(size)) < m*size**2
    n = t+1 if t % 4 == 3 else t-1
    j = next(j for j in range(h//4) if (12*j-n) % h == 0)
    assert j == 1  # Both finite controls require the nonzero Paley remainder.
    residue = Counter({p ^ remainder_shift: j*len(c) for p,c in buckets(paley(11), range(k)).items()})
    if t % 4 == 3:
        reserve_patterns = [(size-1) ^ ((1 << i)-1) ^ reserve_shift for i in range(k)]
    else:
        reserve_patterns = [reserve_shift]*k
        residue[reserve_shift] += 2
    low = {p for p in range(size) if 4*size*len(table[p]) < 3*m}
    assert low and not low.intersection(set(reserve_patterns) | residue.keys())
    remaining = {p: len(table[p])-residue[p]-reserve_patterns.count(p) for p in range(size)}
    assert min(remaining.values()) >= 0
    layers = (n-12*j)//h
    counts = residue.copy()
    for part in partitions:
        use = min(layers, *(remaining[p] for p in part))
        counts.update({p: use for p in part})
        layers -= use
    assert layers == 0
    reserve, selected = select_columns(table, reserve_patterns, counts)
    return assemble(t, source, rows, reserve, selected)


def tensor_control():
    t, k = 257, 16
    m = 2*t-2
    source = sylvester(m)
    rows = list(range(k))
    table = buckets(source, rows)
    assert len(table) == k and all(len(cols) == m//k for cols in table.values())
    first, second = pattern([sign(source[0], r) for r in rows]), pattern([sign(source[1], r) for r in rows])
    assert first != second and k*(k+2) <= m
    counts = {p: m//(2*k)+(p in (first, second)) for p in table}
    reserve_patterns = [first if r % 2 == 0 else second for r in rows]
    return assemble(t, source, rows, *select_columns(table, reserve_patterns, counts))


def verify():
    assert four_control(7) == (20, 190)
    assert four_control(13) == (32, 496)
    print('Uniform Paley controls: four exact added columns for t=7 and t=13')
    cases = (
        (107, paley(211), [1, 40, 108, 178, 194, 206], 0, 1, (222, 24531)),
        (109, double(paley(107)), [6, 28, 62, 70, 163, 189], 4, 2, (226, 25425)),
    )
    for t, source, rows, shift, remainder, expected in cases:
        assert coset_control(t, source, rows, shift, remainder) == expected
    print('Paley coset controls: six exact added columns for t=107 and t=109, both with a 12-column remainder')
    assert tensor_control() == (532, 141246)
    print('Paley tensor control: 1028 × 532, sixteen exact added columns, all 141246 pairs orthogonal')


if __name__ == '__main__':
    verify()
