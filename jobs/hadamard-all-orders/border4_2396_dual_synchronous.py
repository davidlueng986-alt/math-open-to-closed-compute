"""Complete synchronized first-pair exclusion at the low-amplitude dual witness."""

from collections import defaultdict
from decimal import Decimal, localcontext
from io import StringIO
import os
from pathlib import Path
import subprocess
import tempfile

from border4_2396 import periodic
from border4_2396_dual_quotient import LOW_AMPLITUDE_MOD16, dual_words, replay
from border4_2396_nested import nested_negative_words

N = 299
Q = 23
HALF = N // 2
LIMB = (1 << 64) - 1


def compressed(row, q):
    return tuple(sum(row[i::q]) for i in range(q))


def support(row):
    return sum(1 << i for i, x in enumerate(row) if x)


def syndrome(difference, i):
    """Raw mod8 change, divided by four and recorded in inverse lags."""
    return sum((((difference >> ((i + d) % N)) ^ (difference >> ((i - d) % N))) & 1)
               << (d - 1) for d in range(1, HALF + 1))


def sites(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def nullspace(columns):
    echelon = {}
    basis = []
    for j, value in enumerate(columns):
        combination = 1 << j
        while value:
            lead = value.bit_length() - 1
            if lead not in echelon:
                echelon[lead] = value, combination
                break
            other, mask = echelon[lead]
            value ^= other
            combination ^= mask
        else:
            basis.append(combination)
    return basis


def masks_from(basis, positions):
    words = [0]
    for b in basis:
        mask = sum(1 << positions[j] for j in sites(b))
        words.extend([x ^ mask for x in words])
    return words


def construct_decks(heads):
    a, b = map(support, heads)
    overlap, difference = a & b, a ^ b
    assert overlap.bit_count() == 164 and difference.bit_count() == 9
    y0, = {i % Q for i in sites(difference)}
    bit_word = [int(i in {j % 13 for j in sites(difference)}) for i in range(13)]
    assert all(v % 2 == (d == 0) for d, v in enumerate(periodic((bit_word,))))

    columns = {i: syndrome(difference, i) for i in sites(overlap)}
    assert len(nullspace(columns.values())) == 60
    profiles = tuple(compressed(row, Q) for row in heads)

    text = StringIO()
    print(*profiles[0], *profiles[1], file=text)
    unchanged = []
    ranks = []
    profile_counts = []
    for d in range(Q // 2 + 1):
        ys = tuple(sorted({(y0 + d) % Q, (y0 - d) % Q}))
        local = [i for i in sites(overlap) if i % Q in ys]
        basis = nullspace(columns[i] for i in local)
        ranks.append(len(basis))
        initial = tuple(p[y] for p in profiles for y in ys)
        key_to_masks = defaultdict(list)
        for mask in masks_from(basis, local):
            changed = list(initial)
            for j in sites(mask):
                position = ys.index(j % Q)
                changed[position] -= 2 * heads[0][j]
                changed[len(ys) + position] -= 2 * heads[1][j]
            key_to_masks[tuple(changed)].append(mask)
        unchanged.append(key_to_masks[initial])
        profile_counts.append(len(key_to_masks))
        print(len(ys), *ys, file=text)
        print(len(key_to_masks), file=text)
        for key in sorted(key_to_masks):
            print(*key, file=text)

    assert ranks == [1, 1, 1, 13, 1, 1, 1, 1, 1, 13, 13, 13]
    assert sum(ranks) == 60
    assert profile_counts == [2, 2, 2, 814, 2, 2, 2, 2, 2, 792, 686, 804]
    assert list(map(len, unchanged)) == [1, 1, 1, 38, 1, 1, 1, 1, 1, 46, 19, 58]
    return text.getvalue(), [deck for deck in unchanged if len(deck) > 1]


def waveform():
    """Return an integer even vector. Only its literal integer values are used."""
    with localcontext() as context:
        context.prec = 48
        pi = Decimal("3.1415926535897932384626433832795028841971693993751")
        result = []
        for j in range(N):
            z = 2 * pi * min(j, N - j) / N
            term = value = Decimal(1)
            for k in range(1, 28):
                term *= -z * z / ((2 * k - 1) * (2 * k))
                value += term
            result.append((round(100_000 * value) + 5) // 10)
    return result


def gram_input(heads, decks):
    base = waveform()
    odd = [base[(i - 75) % N] - base[(i + 75) % N] for i in range(N)]
    assert max(map(abs, base)) <= 10_000 and max(map(abs, odd)) <= 20_000
    text = StringIO()
    for row in heads:
        print(*row, file=text)
    print(len(decks), file=text)
    for deck in decks:
        print(len(deck), file=text)
        for mask in deck:
            print(*((mask >> (64 * j)) & LIMB for j in range(5)), file=text)

    priority = (
        116, 147, 27, 124, 58, 76, 145, 29, 113, 11, 35, 93, 7, 61, 126, 139,
        79, 62, 45, 101, 108, 22, 47,
    )
    for k in dict.fromkeys((*priority, *range(1, HALF + 1))):
        x, y = ([w[(k * i) % N] for i in range(N)] for w in (base, odd))
        assert sum(a * b for a, b in zip(x, y, strict=True)) == 0
        xnorm, ynorm = (sum(v * v for v in w) for w in (x, y))
        shifted = x + x
        left, right = ([sum(a * b for a, b in zip(w, shifted[i:])) for i in range(N)]
                       for w in (x, y))
        print(k, xnorm, ynorm, 599 * xnorm - 2 * sum(x)**2, file=text)
        print(*left, file=text)
        print(*right, file=text)
    return text.getvalue()


def main():
    s, t = dual_words(LOW_AMPLITUDE_MOD16), nested_negative_words()
    assert periodic(t) == [599] + [0] * (N - 1)
    assert tuple(map(sum, s)) == (0, 1, 0, 0)
    replay(s, t, (477, 113, 80, 652800), 253, 10)
    quotient, decks = construct_decks(s[:2])

    with tempfile.TemporaryDirectory() as path:
        binary = Path(path) / "synchronous"
        source = Path(__file__).with_suffix(".cpp")
        subprocess.run([os.environ.get("CXX", "g++"), "-O3", "-std=c++20",
                        str(source), "-o", str(binary)], check=True)
        subprocess.run([binary, "quotient"], input=quotient, text=True, check=True)
        subprocess.run([binary, "gram"], input=gram_input(s[:2], decks), text=True, check=True)


if __name__ == "__main__":
    main()
