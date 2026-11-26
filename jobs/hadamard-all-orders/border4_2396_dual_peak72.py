"""Replay the peak-72 physical sign source and its fibre and Gram certificates."""

from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
import json
from math import isqrt
import os
from pathlib import Path
import subprocess
import tempfile

from border4_2396 import periodic
from border4_2396_dual_quotient import dual_words, replay
from border4_2396_nested import nested_negative_words
from border4_2396_primitive_field import primitive_factor, remainder

N = 299
HALF = N // 2
SOURCE = Path(__file__).resolve()
PEAK72_MASKS = (
    0x3530280880C047381081844004C1002919440802002A0514288820350019688085404003800,
    0x7009180C1202702481304C0740010590600400403200000E092083000828A001102106208,
    0xB9A0598859C11188011F2008804002020000006008840423110884006010B0A8040300DC80,
    0x3340B3A004EC03008054342018008442231080844018000001010008044013E20046220E684,
)


def verify_source():
    positive, negative = dual_words(PEAK72_MASKS), nested_negative_words()
    assert periodic(negative) == [599] + [0] * (N - 1)
    assert tuple(map(sum, positive)) == (0, 1, 0, 0)
    e = replay(positive, negative, (469, 125, 72, 571392), 261, 9)
    assert 1 + 2 * sum(v % 8 == 0 for v in e[1:]) == 157
    assert sum(v != 0 for v in remainder(e, primitive_factor(11), 11)) == 123
    print("Exact T, C13, C23 and raw mod8. Raw mod16/exact/peak 469/125/72.", flush=True)
    return positive


@lru_cache(None)
def waveform():
    """Deterministic integer test vector. The proof uses only the resulting integers."""
    with localcontext() as context:
        context.prec = 48
        pi = Decimal("3.1415926535897932384626433832795028841971693993751")
        out = []
        for j in range(N):
            z = 2 * pi * min(j, N - j) / N
            term = value = Decimal(1)
            for k in range(1, 28):
                term *= -z * z / ((2 * k - 1) * (2 * k))
                value += term
            out.append((round(100_000 * value) + 50) // 100)
        return tuple(out)


@lru_cache(None)
def gram_data(k):
    base = waveform()
    x = tuple(base[k * i % N] for i in range(N))
    y = tuple(base[(k * i - 75) % N] - base[(k * i + 75) % N] for i in range(N))
    assert sum(u * v for u, v in zip(x, y, strict=True)) == 0
    xnorm, ynorm = (sum(u * u for u in z) for z in (x, y))
    assert xnorm > 0 and ynorm > 0
    cap = 599 * xnorm - 2 * sum(x)**2
    x2 = x + x
    g, h = (tuple(sum(a * b for a, b in zip(z, x2[i:]))
                  for i in range(N)) for z in (x, y))
    return xnorm, ynorm, cap, g, h


@lru_cache(None)
def source_reference(k, word):
    g = gram_data(k)[3]
    nonzero = [(i, a) for i, a in enumerate(word) if a]
    return tuple(sum(a * g[(j - i) % N] for i, a in nonzero) for j in range(N))


def gram_cut(positive, occupied, spec):
    k, rows, reference = spec
    assert 1 <= k <= HALF
    assert rows and tuple(rows) == tuple(sorted(set(rows))) and all(0 <= r < 4 for r in rows)
    x2, y2, cap, g, h = gram_data(k)
    inner = {}
    initial = mass = 0
    if reference is not None:
        assert len(reference) == len(rows)
    for j, row in enumerate(rows):
        if reference is None:
            # Here the integer reference is the current row's convolution against x.
            z = source_reference(k, positive[row])
        else:
            p, q = reference[j]
            assert isinstance(p, int) and isinstance(q, int)
            z = tuple(p * a + q * b for a, b in zip(g, h, strict=True))
            mass += p * p * x2 + q * q * y2
        inner[row] = z
        value = sum(a * b for a, b in zip(positive[row], z, strict=True))
        initial += value
        if reference is None:
            mass += value
    assert mass > 0 and cap >= 0
    coefficients = tuple(2 * positive[row][i] * inner[row][i] if row in inner else 0
                         for row, i in occupied)
    return coefficients, initial - isqrt(cap * mass)


def verify_rational(positive, certificate, quotient=None):
    region = certificate.get("selected")
    fixed_margins = certificate.get("literal", True)
    if quotient is not None:
        assert region is not None and fixed_margins
        assert region == sorted(set(region)) and all(0 <= y < quotient for y in region)
    else:
        assert region is None
    occupied = [(r, i) for r, row in enumerate(positive) for i, a in enumerate(row)
                if a and (region is None or i % quotient in region)]
    objective = int(region is None)
    scale = certificate["denominator"]
    signed = certificate["margin_weights"]
    assert isinstance(scale, int) and scale > 0
    assert len(signed) == (4 * (13 + 23) if fixed_margins else 4)
    assert all(isinstance(v, int) for v in signed)

    combined = [positive[r][i] * (signed[36*r + i % 13] + signed[36*r + 13 + i % 23]
                                  if fixed_margins else signed[r])
                for r, i in occupied]
    rhs = 0
    for spec, multiplier in certificate["inequalities"]:
        assert isinstance(multiplier, int) and multiplier >= 0
        coefficients, b = gram_cut(positive, occupied, spec)
        rhs += multiplier * b
        combined = [a + multiplier * c for a, c in zip(combined, coefficients, strict=True)]
    bound = Fraction(rhs - sum(max(0, c - scale * objective) for c in combined), scale)
    assert bound == Fraction(*certificate["value"])
    return bound


def check_gram(positive, certificates):
    hamming = certificates["hamming"]
    assert len(hamming) == 2 and [case["literal"] for case in hamming] == [False, True]
    for minimum, case in zip((32, 36), hamming, strict=True):
        bound = verify_rational(positive, case)
        assert bound > minimum - 2
        print(f"Even Hamming distance at least {minimum}, rational lower bound {float(bound):.9f}.",
              flush=True)
    regions = {}
    for q in (13, 23):
        cases = certificates["fibres"][str(q)]
        assert all(verify_rational(positive, case, q) > 0 for case in cases)
        regions[q] = {tuple(case["selected"]) for case in cases}
        assert len(regions[q]) == len(cases)
    return regions


def check_fibres(positive, regions):
    payload = "\n".join(" ".join(map(str, row)) for row in positive)
    cases = (
        (23, 3, 0, (1771, 63, 0, 0, 18)),
        (13, 2, 0, (78, 6, 0, 0, 22)),
        (23, 4, 1, (8855, 719, 0, 32, 38)),
        (13, 3, 1, (286, 40, 0, 4, 43)),
    )
    with tempfile.TemporaryDirectory() as path:
        binary = Path(path) / "peak72_fibres"
        subprocess.run([os.environ.get("CXX", "g++"), "-std=c++20", "-O3",
                        str(SOURCE.with_suffix(".cpp")), "-o", str(binary)], check=True)
        for q, size, fixed, expected in cases:
            result = subprocess.run([binary, str(q), str(size), str(fixed)], input=payload,
                                    capture_output=True, text=True, check=True)
            *unresolved, last = [line.split() for line in result.stdout.splitlines()]
            assert last[0] == "counts" and tuple(map(int, last[1:])) == expected
            assert len(unresolved) == expected[3]
            assert all(c[0] == "unresolved" and len(c) == size + 1 for c in unresolved)
            remaining = {tuple(map(int, row[1:])) for row in unresolved}
            assert remaining == (regions[q] if fixed else set())
            print(f"C{q}, at most {size} fibres, literal margins {bool(fixed)}, "
                  f"{expected[0]} cases, {expected[1]} linearly consistent, "
                  f"{len(unresolved)} closed by Gram.", flush=True)


def main():
    positive = verify_source()
    certificates = json.loads(SOURCE.with_name(SOURCE.stem + "_gram.json").read_text())
    regions = check_gram(positive, certificates)
    check_fibres(positive, regions)


if __name__ == "__main__":
    main()
