"""Check the full-y 118-bit frame and two exact changed-margin branch censuses."""

import argparse
from pathlib import Path
import subprocess
import tempfile

from border4_2396 import periodic
from border4_2396_493 import product_mod2, reducer, reverse_mod2
from border4_2396_changed_margins import CHANGED_MARGINS
from border4_2396_exact_negative import word
from border4_2396_fixed_first import incident, reflect
from border4_2396_nested import nested_negative_words
from border4_2396_shifted_tail import compress, verify_lift

N = 299
Q = 13
H = N // 2
POSITIVE_Y = (3, 9, 10, 11)
W = (3, 9, 10, 11, 12, 13, 14, 20)
Q_MASK = sum(1 << i for i in (6, 8, 11, 12))
RELATION = ((10, 13), (0, 3, 9, 10, 13, 14, 20))
EXPECTED = {
    "independent": [(0, 1, 0, 0, 0), (1, 15748, 0, 0, 0), (2, 207474692, 67, 1, 0),
                    (3, 1835353845456, 436748, 16881, 0)],
    "center": [(0, 616, 0, 0, 0), (1, 30834328, 10, 1, 0)],
}


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def set_mask(sites):
    return sum(1 << i for i in sites)


def occupy(row):
    return {i for i, v in enumerate(row) if v}


def site(x, y):
    return (92*x + 208*y) % N


def packed(mask):
    return tuple((mask >> (64*i)) & ((1 << 64)-1) for i in range(3))


def verify_frame(positive):
    u = set_mask(i for i, v in enumerate("+--.+++++......+++--.+-") if v != ".")
    v = u ^ 1
    r = ((1 << Q) - 1) ^ Q_MASK
    assert product_mod2(r, reverse_mod2(r, Q), Q) == 1
    assert tuple(i for i in range(23) if not (u >> i & 1)) == W
    assert all(abs(a) == 1 - ((r >> (i % Q)) & (c >> (i % 23)) & 1)
               for row, c in zip(positive[:2], (u, v), strict=True) for i, a in enumerate(row))

    def columns(values):
        return [product_mod2(c, 1 << j, 23) for c in (u, v) for j in values]

    assert reducer(enumerate(columns(W)))[0] == 16
    extended = (0, *W)
    assert reducer(enumerate(columns(extended)))[0] == 17
    left, right = (set_mask(a) for a in RELATION)
    assert reverse_mod2(left, 23) == left and reverse_mod2(right, 23) == right
    assert product_mod2(u, left, 23) == product_mod2(v, right, 23)
    r_squared = product_mod2(r, r, Q)
    transform = [product_mod2(r_squared, reverse_mod2(z, Q), Q) for z in range(1 << Q)]
    assert all(transform[w] == z for z, w in enumerate(transform))
    fixed = [i for i, a in enumerate(transform) if i == a]
    assert len(fixed) == 128 and [z for z in fixed if not z & ~Q_MASK] == [0, Q_MASK]
    raw = [incident(occupy(row), i) for row in positive[:2] for i in occupy(row)
           if i % 23 in extended]
    assert len(raw) == 225 and reducer(enumerate(raw))[0] == 107
    return transform


def prepare(positive, transform):
    a, b = positive[2], reflect(positive[3])
    x = tuple((u + v) // 2 for u, v in zip(a, b, strict=True))
    y = tuple((u - v) // 2 for u, v in zip(a, b, strict=True))
    p, q = occupy(x), occupy(y)
    active = sorted(p | q)
    assert set(active) == occupy(a) == occupy(b) and len(active) == 130
    assert reducer((i, incident(set(active), i)) for i in active)[0] == 129
    assert not p & q and sum(x) == sum(y) == 0

    rank, reduce = reducer((i, incident(support, i) | (1 << (H + g)))
                           for g, support in enumerate((p, q)) for i in support)
    assert rank == 128
    quotient_bits = sorted({j for i in range(H+2) for j in indices(reduce(1 << i)[0])})
    assert len(quotient_bits) == 23
    packing = {i: j for j, i in enumerate(active)}

    def encode(mask):
        r, f = reduce(mask)
        code = sum(((r >> j) & 1) << k for k, j in enumerate(quotient_bits))
        lift = set_mask(packing[i] for i in indices(f))
        return (code, *packed(lift))

    corr = periodic(positive)[1:H+1]
    assert all((v + 2) % 4 == 0 for v in corr)
    origin = sum(((v + 2)//4 % 2) << i for i, v in enumerate(corr))
    lines = [POSITIVE_Y, transform, encode(origin)]
    lines.extend(encode(1 << i) for i in range(H))
    lines.extend(positive[:2])
    for row in (x, y):
        lines.append(compress(row))
        for j in (-1, *range(Q)):
            mask = [set_mask(k for k, i in enumerate(active)
                             if row[i] == sign and (j < 0 or i % Q == j))
                    for sign in (1, -1)]
            lines.append(packed(mask[0]) + packed(mask[1]))
    return "\n".join(" ".join(map(str, row)) for row in lines) + "\n", active, (x, y)


def verify_output(mode, output, positive, negative, transform, active, phases):
    data = list(map(int, output.read_text().split()))
    masks = [0, 0]
    if mode == "center":
        energy, a, b, block, f, *flip = data
        k = b ^ transform[b]
        for r, center in enumerate((a, b)):
            masks[r] = set_mask(site(i, 0) for i in indices(center))
            masks[r] |= set_mask(site(i, (-y) % 23) for y in POSITIVE_Y if y in RELATION[r]
                                 for i in indices(k))
        moves = [(block, f)] if block >= 0 else []
    else:
        energy, count, *options = data
        moves = list(zip(options[:2*count:2], options[1:2*count:2], strict=True))
        flip = options[2*count:]
    for block, f in moves:
        r, k = divmod(block, 4)
        y = POSITIVE_Y[k]
        masks[r] ^= set_mask(site(x, y) for x in indices(f))
        masks[r] ^= set_mask(site(x, (-y) % 23) for x in indices(transform[f]))

    assert len(flip) == 3
    f = sum(v << (64*k) for k, v in enumerate(flip))
    tail = set_mask(active[i] for i in indices(f))

    def switch(row, mask):
        return tuple(-a if mask >> i & 1 else a for i, a in enumerate(row))

    result = tuple(switch(w, mask) for w, mask in zip(positive[:2], masks, strict=True))
    x, y = (switch(w, tail) for w in phases)
    result += (tuple(a+b for a, b in zip(x, y, strict=True)),
               reflect(tuple(a-b for a, b in zip(x, y, strict=True))))
    assert tuple(map(compress, result[:2])) != tuple(map(compress, positive[:2]))
    assert sum(v*v for v in (
        a - (553 if d == 0 else -46)
        for d, a in enumerate(periodic(tuple(map(compress, result))))
    )) == energy
    patterns = tuple("".join(".+-"[0 if a == 0 else (1 if a > 0 else 2)] for a in row)
                     for row in result)
    if mode == "center":
        assert energy == 33408
        verify_lift(patterns, negative, [16, 32, 64, -40, -96, 24, 8], 597, 105, 96, 931840)
    else:
        assert energy == 1792
        verify_lift(patterns, negative, [0, 16, 0, 0, 8, -24, 0], 597, 125, 80, 585728)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--scope", choices=("both", "independent", "center"), default="both")
    args = parser.parse_args()
    negative = nested_negative_words()
    positive = verify_lift(CHANGED_MARGINS, negative, [0]*7, 509, 109, 88, 700928)
    transform = verify_frame(positive)
    source, active, last = prepare(positive, transform)
    checker = Path(__file__).with_suffix(".cpp")
    with tempfile.TemporaryDirectory() as directory:
        binary = Path(directory) / "verify_full_y"
        subprocess.run(["g++", "-O3", "-std=c++20", str(checker), "-o", str(binary)], check=True)
        scopes = ("center", "independent") if args.scope == "both" else (args.scope,)
        for mode in scopes:
            output = Path(directory) / (mode + ".out")
            run = subprocess.run([str(binary), mode, str(output)], input=source, text=True,
                                 check=True, capture_output=True)
            observed = [tuple(map(int, row.split())) for row in run.stdout.splitlines()
                        if row[:1].isdigit()]
            assert observed == EXPECTED[mode]
            verify_output(mode, output, positive, negative, transform, active, last)
            print(mode, "verified exhaustive counts", observed)


if __name__ == "__main__":
    main()
