"""Exact conference doubling and a composite Paley exterior witness."""

from itertools import combinations
from math import isqrt

from r_paley_uniform_growth import SKEW_FOUR, buckets, pattern, select_columns, sign
from verify import paley, rows_from_columns, verify_orthogonal


H_TWO = ((1, 1), (1, -1))
J_TWO = ((0, 1), (-1, 0))


def prime(n):
    return n > 1 and all(n % p for p in range(2, isqrt(n)+1))


def skew_paley(q):
    assert prime(q) and q % 4 == 3
    squares = {x*x % q for x in range(1, q)}
    core = [tuple(0 if i == j else 1 if (j-i) % q in squares else -1 for j in range(q))
            for i in range(q)]
    return [(0,)+(1,)*q] + [(-1,)+row for row in core]


def double(conference):
    return [tuple(H_TWO[a][b]*value + J_TWO[a][b]*(i == j)
                  for j, value in enumerate(row) for b in range(2))
            for i, row in enumerate(conference) for a in range(2)]


def check_conference(conference):
    n = len(conference)
    assert all(len(row) == n and row[i] == 0 and sum(x == 0 for x in row) == 1
               and all(x in (-1, 0, 1) for x in row) for i, row in enumerate(conference))
    assert all(conference[i][j] == -conference[j][i] for i, j in combinations(range(n), 2))
    masks = [sum((x == 1) << i for i, x in enumerate(row)) for row in conference]
    full_mask = (1 << n)-1
    assert all(n-2 == 2*((masks[i] ^ masks[j]) & (full_mask ^ (1 << i) ^ (1 << j))).bit_count()
               for i, j in combinations(range(n), 2))
    return n*(n-1)//2


def normalize(conference):
    signs = (1,)+conference[0][1:]
    normalized = [tuple(signs[i]*x*signs[j] for j, x in enumerate(row))
                  for i, row in enumerate(conference)]
    assert normalized[0] == (0,)+(1,)*(len(conference)-1)
    core = [row[1:] for row in normalized[1:]]
    assert not any(map(sum, core)) and not any(map(sum, zip(*core, strict=True)))
    return core


def construct(t, core, source):
    m, n = 2*t-2, 4*t
    assert verify_orthogonal(m, source) == m*(m-1)//2
    rows = [0, 1, 2, 3]
    table = buckets(source, rows)
    if len(table[0]) > len(table[1]):
        source = [c ^ (1 << rows[-1]) for c in source]
        table = buckets(source, rows)
    target = (t+1)//4
    odd = min(target, len(table[1])-1)
    counts = {p: odd if p.bit_count() % 2 else target-odd for p in range(8)}
    reserve_type = [pattern(list(col)) for col in zip(*SKEW_FOUR, strict=True)]
    reserve, selected = select_columns(table, reserve_type, counts)
    gamma, *w = selected
    source = list(source)
    mask = (1 << m)-1
    for r, c in zip(rows, reserve, strict=True):
        if sign(source[c], r) != sign(source[gamma], r):
            source[c] ^= mask
    normalized = [mask ^ source[gamma] ^ c for c in source]
    lower = [normalized[i] for i in w]
    assert len(lower) == t and all(x.bit_count() == m//2 for x in lower)

    outside_border = 1 << (n-2)
    inside_border = 3 << (n-2)
    left, right = [], []
    for j, (col, word) in enumerate(zip(zip(*core, strict=True), lower, strict=True)):
        minus_diag = sum((x == 1) << r for r, x in enumerate(col))
        plus_diag = minus_diag | (1 << j)
        left.append(plus_diag | (minus_diag << t) | (word << (2*t)) | outside_border)
        right.append(minus_diag | (plus_diag << t) | ((word ^ mask) << (2*t)) | outside_border)
    outside = left + right

    inside = [(1 << n)-1, (mask << (2*t)) | inside_border]
    low_t = (1 << t)-1
    for r, c in zip(rows, reserve, strict=True):
        assert sign(normalized[c], r) == 1
        word = normalized[c] ^ (1 << r)
        top = sum((sign(x, r) == 1) << i for i, x in enumerate(lower))
        inside.append(top | ((top ^ low_t) << t) | (word << (2*t)) | inside_border)
    return outside, inside


def check_residual_arithmetic():
    q, period, t = 227, 63600, 455
    assert prime(q) and q % 4 == 3 and t == 2*q+1
    assert all(prime(p) for p in (5, 7, 13, 17, 107, 3, 101, 11, 907))
    assert t == 5*7*13 and 4*t-1 == 17*107 and 2*t-1 == 3**2*101
    assert 16*t+1 == 7281 and (16*t+1) % 11 not in {x*x % 11 for x in range(11)}
    assert all(pow(q, period, modulus) == 1 for modulus in (4, 5, 7, 17, 107, 3, 101, 11))

    q, period, t = 805019, 63540540, 1610039
    assert all(prime(p) for p in (q, 109, 14771, 13, 479))
    assert q % 201180 == 299 and q % 4 == 3 and t == 2*q+1 == 109*14771
    assert t % 100590 == 599 and (4*t-1) % (5*479) == (2*t-1) % (3*7) == 0
    assert (16*t+1) % 13 == 7 and 7 not in {x*x % 13 for x in range(13)}
    assert all(pow(q, period, modulus) == 1 for modulus in (201180, 109, 14771, 13))
    print('Skew doubling crosses the residual set: two composite exponent families, one at t == 599 mod 100590')


def verify():
    check_residual_arithmetic()
    seed = skew_paley(227)
    assert check_conference(seed) == 25878
    conference = double(seed)
    assert len(conference) == 456 and check_conference(conference) == 103740
    t = len(conference)-1
    assert t == 455 and 2*t-3 == 907
    outside, inside = construct(t, normalize(conference), paley(907))
    incidence = [c & ((1 << (4*t-2))-1) for c in outside]
    blocks = rows_from_columns(4*t-2, incidence)
    assert len(set(blocks)) == 4*t-2 and all(b.bit_count() == t for b in blocks)
    block_mask = (1 << (2*t))-1
    distinct = set(blocks)
    assert all((b ^ block_mask) not in distinct for b in blocks)
    assert all(c.bit_count() == 2*t-1 for c in incidence)
    assert all((a & b).bit_count() == t-1 for a, b in combinations(incidence, 2))
    print('R(455): 1818 distinct blocks on 910 points, all 413595 point pairs verified')
    assert len(outside + inside) == 916 and verify_orthogonal(4*t, outside + inside) == 419070
    print('Hadamard 1820 × 916: all 419070 column pairs orthogonal')


if __name__ == '__main__':
    verify()
