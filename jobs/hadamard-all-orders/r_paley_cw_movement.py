"""Check rational duals for every fresh CW row/reserve pair without an LP solver."""

from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from struct import Struct
from zlib import decompress

from r_paley_cooper_wallis import build_pair, build_source
from r_paley_cooper_wallis_growth import ONE_FLIPS, SELECTED
from r_paley_cw_four_trade import HEIGHT, inventory, raw_domains
from r_paley_isotropic_code import assemble
from verify import verify_orthogonal

CERTIFICATE = Struct("<HHBB67h")
DATA_FILE = "r_paley_cw_movement_duals.zlib"


def sign_difference(shape, left, right):
    return ((shape >> left) ^ (shape >> right)) & 1


def verify():
    source = build_source()
    far, _ = build_pair(source)
    selected = [j for j in range(HEIGHT) if SELECTED >> j & 1]
    originals = [*far, *(source[g] ^ (1 << r) for r, g in ONE_FLIPS)]
    assembly = assemble(599, source, selected, originals)
    assert len(assembly) == 1211 and verify_orthogonal(2396, assembly) == 732655
    decks, rows, roots, reserves, _, labels, max_reuse = inventory(source, far, selected)
    assert max_reuse == 418
    old = set(selected)
    eligible = sorted(labels)
    assert len(eligible) == 701
    domain = raw_domains(source, far, decks, rows, roots, reserves)
    expected = {(r, g): vector for r, pivots in domain.items() for g, vector in pivots}
    assert len(expected) == 1377

    old_shape = {j: labels[j] << 1 for j in eligible}
    first_negative = sum((decks[0][j] < 0) << j for j in eligible)
    n = len(ONE_FLIPS) + 3
    assert n == 12
    pairs = tuple(combinations(range(n), 2))
    old_count = {i: sum(sign_difference(old_shape[j], a, b) for j in selected)
                 for i, (a, b) in enumerate(pairs, 1) if b < n - 1}
    row_indices = [[i for i, (a, b) in enumerate(pairs, 1) if sign_difference(word, a, b)]
                   for word in range(1 << n)]

    data = Path(__file__).with_name(DATA_FILE).read_bytes()
    payload = decompress(data)
    assert len(payload) == CERTIFICATE.size * len(expected)
    status = Counter()
    previous_row = -1
    group = None
    for r, g, exponent, flag, *numerator in CERTIFICATE.iter_unpack(payload):
        assert 0 <= exponent <= 28 and flag in (0, 1)
        required = expected.pop((r, g))
        if r != previous_row:
            previous_row = r
            columns = defaultdict(lambda: [0, 0])
            raw = rows[r] ^ first_negative
            for j in eligible:
                shape = old_shape[j] | (((raw >> j) & 1) << (n - 1))
                columns[shape][int(j not in old)] += 1
            group = columns, raw
        columns, raw = group
        scale = 1 << exponent
        rhs = [600]
        for i, (a, b) in enumerate(pairs, 1):
            target = required[a] if b == n - 1 else 0
            assert target % 2 == 0
            rhs.append((600 - target) // 2 if b == n - 1 else old_count[i])
        bound = sum(a * b for a, b in zip(numerator, rhs, strict=True))
        remove = (old_shape[g] | (((raw >> g) & 1) << (n - 1))) if g in old_shape else -1
        for shape, count in columns.items():
            inside, outside = count
            if shape == remove:
                inside -= int(g in old)
                outside -= int(g not in old)
            value = numerator[0] + sum(numerator[i] for i in row_indices[shape])
            bound += inside * min(0, -value)
            bound += outside * min(0, (0 if flag else scale) - value)
        assert bound > (0 if flag else 9 * scale)
        status[flag] += 1
    assert not expected and status == {0: 1197, 1: 180}
    print("CW 1211, all 1377 fresh raw row/reserve pairs covered")
    print("180 incompatible with every selected exterior, remaining 1197 require at least 10 substitutions")
    print(f"Exact dual data SHA256 {sha256(data).hexdigest()}")


if __name__ == "__main__":
    verify()
