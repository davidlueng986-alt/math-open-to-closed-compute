"""Rebuild a full mod-32 pairing with one exact Walsh odd-modulus check."""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path

from stack_1197_four_channels import LOWER_OMITTED, sources
from stack_1198_channels import signatures
from stack_1198_four_channel_compressed import SYLVESTER, dot as inner
from stack_1198_four_channel_mod32 import rebuild
from stack_1198_four_channels import conference_graph_columns, sorted_pairing
from stack_1198_joint import dot
from verify import verify_orthogonal


def pair_words(upper, lower, u, v, x, y, updates):
    n, m = len(upper), len(lower)
    top, top_keys = signatures(upper, u, x)
    bottom, bottom_keys = signatures(lower, v, y)
    desired = {j: top_keys[i][1] for i, j in sorted_pairing(top_keys, bottom_keys).items()}
    assert desired.keys() == set(range(m)) - set(LOWER_OMITTED)
    assert updates.keys() <= desired.keys()
    assert all(desired[j] != q for j, q in updates.items())
    desired.update(updates)
    stock = defaultdict(list)
    for i, signature in enumerate(top_keys):
        stock[signature].append(i)
    old = [None] * n
    r = [0] * m
    all_bits = (1 << m) - 1
    for j, q in sorted(desired.items()):
        p, t = bottom[j]
        i = stock[abs(p), q if p else abs(q)].pop()
        a, b = top[i]
        r[j] = t - (q if p >= 0 else -q)
        sign = next(sign for sign in (1, -1) if a + sign * p == 0 and sign * b + t == r[j])
        old[i] = upper[i] | ((lower[j] if sign > 0 else lower[j] ^ all_bits) << n)
    assert all(not copies for copies in stock.values())
    return [*old, u | v << n], r


def admissible_forms(first):
    for candidate in product((-1, 0, 1), repeat=4):
        active = [value for value in candidate if value]
        if len(active) == 3 and active[0] > 0 and all(
                (first[i] * candidate[j] - first[j] * candidate[i]) % 3
                for i, j in combinations(range(4), 2)):
            yield candidate


def odd_checks(r, first, second):
    sites = list(zip(*(r[c:c + 300] for c in range(0, 1200, 300)), strict=True))
    assert sum(any(site) for site in sites) == 94
    w = [tuple(inner(row, site) for row in SYLVESTER) for site in sites]
    assert all(v % 16 == 0 for site in w for v in site)
    walsh = [tuple(v // 16 for v in site) for site in w]
    assert all(sum(v) % 2 == 0 for v in zip(*walsh, strict=True))
    assert not any(inner(first, site) for site in walsh)
    assert Counter(sum(t != 0 for t in row) for row in walsh) == {0: 206, 1: 78, 2: 16}

    graph = conference_graph_columns()
    candidates = list(admissible_forms(first))
    assert len(candidates) == 6 and second in candidates
    scores = []
    for form in candidates:
        vec = [inner(form, site) for site in walsh]
        odd = [sum(col[j] * value for col, value in zip(graph, vec, strict=True)) % 25
               for j in range(150)]
        scores.append((sum(a != 0 for a in odd), sum(value * value for value in vec), form))
    assert min(scores) == (141, 106, second)
    assert 106 < 150
    for local in product(range(-2, 3), repeat=4):
        transformed = tuple(inner(row, local) for row in SYLVESTER)
        if all(a % 4 == 0 for a in transformed):
            u = tuple(a // 4 for a in transformed)
            assert (not any(u)) == (inner(first, u) % 3 == inner(second, u) % 3 == 0)
    return min(scores)[:2]


def verify():
    path = Path(__file__).with_name('stack_1198_four_channel_odd_one_data.json')
    record = json.loads(path.read_text(encoding='ascii'))
    upper, lower, u, v = sources()
    first_old, candidate, prior_lower, _ = rebuild()
    n, m = len(upper), len(lower)
    assert prior_lower == lower and first_old[-1] == u | v << n
    x, y = candidate & ((1 << n) - 1), candidate >> n
    updates = {int(j): q for j, q in record['signed_second_updates'].items()}
    assert len(updates) == 435
    old, r = pair_words(upper, lower, u, v, x, y, updates)
    assert verify_orthogonal(n + m, old) == 715806
    assert Counter(abs(dot(n + m, column, candidate)) for column in old) == {0: 853, 4: 312, 8: 32}
    assert tuple(sum(v * v for v in r[c:c + 300]) for c in range(0, m, 300)) == (2016, 1248, 1888, 1888)
    assert all(sum((value // 4) * (2 * (col >> i & 1) - 1)
                   for col, value in zip(lower, r, strict=True)) % 8 == 0 for i in range(m))
    f, g = tuple(record['zero_form']), tuple(record['next_form'])
    assert (f, g) == ((1, -1, 1, 0), (1, 0, -1, 1))
    odd_checks(r, f, g)
    digest = sha256(''.join(f'{word:x}\n' for word in [*old, candidate]).encode('ascii')).hexdigest()
    assert digest == '6d478096b94b1c9781ca4bb7232cbf408b822f78a6c07f2eba8d41a61537886c'
    print('Four-channel E7040: full auxiliary numerator modulo 32; one exact Walsh modulo-25 check')
    print('Compatible remaining Walsh check: squared norm 106; 141 of 150 conference equations fail')
    print('Four-channel E7040 packed SHA256', digest)


if __name__ == '__main__':
    verify()
