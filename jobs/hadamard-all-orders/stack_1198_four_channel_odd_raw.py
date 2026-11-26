"""Verify changed lower raw words with a preserved exact odd Walsh check."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

from stack_1197_four_channels import LOWER_OMITTED, sources
from stack_1198_four_channel_compressed import SYLVESTER, dot as inner
from stack_1198_four_channel_mod32 import rebuild
from stack_1198_four_channel_odd_one import admissible_forms, pair_words
from stack_1198_four_channels import SHARP_CAP_LOWER, conference_graph_columns
from stack_1198_joint import dot
from verify import verify_orthogonal


FIRST_FORM = (1, -1, 1, 0)


def companion_scores(residuals):
    sites = list(zip(*(residuals[j:j + 300] for j in range(0, 1200, 300)), strict=True))
    transformed = [tuple(inner(row, site) for row in SYLVESTER) for site in sites]
    assert all(t % 16 == 0 for site in transformed for t in site)
    walsh = [tuple(t // 16 for t in site) for site in transformed]
    assert all(sum(channel) % 2 == 0 for channel in zip(*walsh, strict=True))
    assert all(inner(FIRST_FORM, site) == 0 for site in walsh)
    graph = conference_graph_columns()
    scores = []
    for second in admissible_forms(FIRST_FORM):
        vector = [inner(second, site) for site in walsh]
        norm = sum(t * t for t in vector)
        failures = sum(sum(column[j] * t for column, t in zip(graph, vector, strict=True)) % 25 != 0
                       for j in range(150))
        scores.append((norm, failures, second))
    assert len(scores) == 6
    return sum(any(site) for site in sites), min(scores), min(scores, key=lambda t: (t[1], t[0], t[2]))


def replay(case, upper, lower, u, v, x, y0):
    n, m = len(upper), len(lower)
    removed, inserted = case['lower_move']
    assert removed in SHARP_CAP_LOWER and inserted not in SHARP_CAP_LOWER
    assert 900 <= removed < m and 900 <= inserted < m
    y = y0 ^ (1 << removed) ^ (1 << inserted)
    assert dot(n, u, x) == dot(m, v, y) == 0
    assert m - dot(m, y, lower[30]) == 68
    assert [dot(m, y, lower[j]) for j in LOWER_OMITTED] == [-36, 8, 68, -60]

    updates = {int(j): q for j, q in case['updates'].items()}
    old, residuals = pair_words(upper, lower, u, v, x, y, updates)
    assert verify_orthogonal(n + m, old) == 715806
    candidate = x | (y << n)
    assert Counter(abs(dot(n + m, c, candidate)) for c in old) == {
        int(value): count for value, count in case['histogram'].items()
    }
    assert max(map(abs, residuals)) == 8 and all(q % 4 == 0 for q in residuals)
    assert [sum(q * q for q in residuals[j:j + 300]) for j in range(0, m, 300)] == case['channels']
    nonzero = [(q, col) for q, col in zip(residuals, lower, strict=True) if q]
    assert all(sum(q * (2 * (col >> i & 1) - 1) for q, col in nonzero) % 32 == 0 for i in range(m))
    active, least_norm, least_failures = companion_scores(residuals)
    assert active == case['active'] and least_norm[0] < 150 and least_failures[0] < 150
    assert [*least_norm[:2], list(least_norm[2])] == case['companion_norm']
    assert [*least_failures[:2], list(least_failures[2])] == case['companion_failures']
    digest = sha256(''.join(f'{col:x}\n' for col in [*old, candidate]).encode('ascii')).hexdigest()
    assert digest == case['sha256']
    energy = sum(case['channels'])
    print(f'Changed lower {removed}->{inserted}: mod32, exact first odd check, cap8, E{energy}')
    print(f'Changed lower E{energy}: {active} active sites, least norm {least_norm}, least failures {least_failures}')


def verify():
    fixture = Path(__file__).with_name('stack_1198_four_channel_odd_raw_data.json')
    records = json.loads(fixture.read_text(encoding='ascii'))
    upper, lower, u, v = sources()
    old, candidate, prior_lower, _ = rebuild()
    n = len(upper)
    assert prior_lower == lower and old[-1] == u | (v << n)
    assert [r['lower_move'] for r in records] == [[961, 1153], [961, 1081], [961, 1081]]
    assert [sum(r['channels']) for r in records] == [7552, 7680, 9472]
    for case in records:
        replay(case, upper, lower, u, v, candidate & ((1 << n) - 1), candidate >> n)


if __name__ == '__main__':
    verify()
