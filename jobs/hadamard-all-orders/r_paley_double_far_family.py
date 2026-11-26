"""Replay the conditional double-far family and its two explicit orders."""

from hashlib import sha256

from r_paley_double_far import DIGEST, SELECTOR, WILLIAMSON, build_pair, build_source, fibres
from r_paley_far_family import quaternion_basis
from r_paley_isotropic_code import assemble
from verify import goethals_seidel, signs, verify_orthogonal

T5 = ((0, 1), (1, -1), (1, 1), (3, -1), (3, -1))
DIGEST_524 = "c2b0a523e56c03f43a6fdd997ba246d47220b48b34ab6c530e9cb586219bc3a5"

COEFFICIENTS = (
    {(-74, -52), (-18, 0), (-14, 0), (-2, 0), (2, 0), (6, 0), (10, 0), (74, -52)},
    {(-74, -52), (-74, 52), (-14, 0), (-10, 0), (-2, 0), (2, 0), (6, 0), (10, 0), (18, 0)},
)


def dot(n, left, right):
    return n - 2 * (left ^ right).bit_count()


def compressed_data():
    source = build_source()
    raw, _ = build_pair(source)
    group = fibres()
    lines = tuple(sum(((word >> fibre[0]) & 1) << j for j, fibre in enumerate(group)) for word in raw)
    assert dot(52, *lines) == 0

    base = tuple(map(signs, WILLIAMSON))
    units = tuple(quaternion_basis(*entry) for entry in zip(*base))
    short = [
        goethals_seidel([tuple(row[u][j] for row in units) for j in range(4)])
        for u in range(4)
    ]
    deck = [
        tuple(tuple(dot(52, word, col) for col in H) for H in short) for word in lines
    ]
    coeff = [
        tuple((a - 2 * d, b + c) for a, b, c, d in zip(*values, strict=True))
        for values in deck
    ]
    assert tuple(set(values) for values in coeff) == COEFFICIENTS
    eligible = [{j for j, (a, b) in enumerate(entry) if b == 0 and abs(a) == 2}
                for entry in coeff]
    assert [len(x) for x in eligible] == [33, 33]
    common = eligible[0] & eligible[1]
    assert len(common) == 32
    assert sum(coeff[0][j][0] == coeff[1][j][0] for j in common) == 16
    print("Paley double-far family: 32 invariant eligible classes, split 16 and 16")
    return lines, units, coeff


def replay(parameter, selector, expected_digest, data):
    lines, units, coeff = data
    e = len(selector)
    assert e == 2 * parameter**2 + 5 and e % 13 != 0
    assert all(0 <= k < 4 and abs(v) == 1 for k, v in selector)
    assert tuple(sum(v for k, v in selector if k == j) for j in range(4)) == (
        1, parameter, parameter, -2,
    )
    assert all(sum(a * b for (i, a), (j, b) in zip(selector, selector[shift:]) if i == j) == 0
               for shift in range(1, e))
    block = 13 * e
    size = 4 * block
    t = 26 * e + 1
    words = [[] for _ in range(4)]
    for r in range(block):
        unit, phase = selector[r % e]
        for line, value in zip(words, units[r % 13][unit], strict=True):
            line.append(phase * value)
    source = goethals_seidel(words)
    assert verify_orthogonal(size, source) == size * (size - 1) // 2

    index = tuple((r // block) * 13 + (r % block) % 13 for r in range(size))
    raw = [sum(((w >> j) & 1) << r for r, j in enumerate(index)) for w in lines]
    assert dot(size, *raw) == 0
    decks = [tuple(dot(size, w, h) for h in source) for w in raw]
    for deck, values in zip(decks, coeff, strict=True):
        assert deck == tuple(values[j][0] + parameter * values[j][1] for j in index)
        assert sum(abs(a) == 2 for a in deck) == 33 * e
        assert max(map(abs, deck)) == 74 + 52 * abs(parameter)
    same = [j for j, (a, b) in enumerate(zip(*decks, strict=True)) if abs(a) == 2 and a == b]
    opposite = [j for j, (a, b) in enumerate(zip(*decks, strict=True)) if abs(a) == 2 and a == -b]
    assert len(same) == len(opposite) == 16 * e
    need = 13 * e + 1
    selected = sorted(same[:need] + opposite[:need])

    columns = assemble(t, source, selected, raw)
    assert len(columns) == 2 * t + 4
    pairs = verify_orthogonal(4 * t, columns)
    assert pairs == len(columns) * (len(columns) - 1) // 2
    digest = sha256(b"".join(col.to_bytes((4 * t + 7) // 8, "little") for col in columns)).hexdigest()
    assert digest == expected_digest
    distance = 26 * e - 37 - 26 * abs(parameter)
    print(f"Paley double-far family: {4*t} x {len(columns)}, "
          f"both distances {distance}, {pairs} exact column products")
    print("SHA256", digest)


def verify():
    data = compressed_data()
    replay(0, T5, DIGEST_524, data)
    replay(-3, SELECTOR, DIGEST, data)


if __name__ == "__main__":
    verify()
