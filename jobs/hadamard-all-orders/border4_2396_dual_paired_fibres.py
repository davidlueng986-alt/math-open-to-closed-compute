"""Reconstruct two peak-48 witnesses and exhaust their paired-fibre switch families."""

from itertools import combinations, product
import os
from pathlib import Path
import subprocess
import tempfile

from border4_2396 import periodic
from border4_2396_dual_peak48 import PEAK48_MASKS, check_primitive_norm
from border4_2396_dual_quotient import dual_words, replay
from border4_2396_nested import nested_negative_words
from border4_2396_primitive_field import primitive_factor

N = 299
LIMB = (1 << 64) - 1
FIRST_DOUBLED = (
    0x10000004000041000010400004000201000480000120000048000010000000000000000000,
    0,
    0x200000480000100000000000000000000000000000000000000000000000000000000000000,
    0x240000080000000000000000000000000000000000000000000000000000000000000200000,
)
SECOND_DOUBLED = (
    0x400000000000000002000004000000000040000000000100000000000000000a00001000000,
    0x2400004000408000810001000082000000010000000000000000400000800080004100000,
    0x4000000000000400000000000000000000000000200000000000020000000000000,
    0x1000000000000100000000000000000000000000080000000000008,
)


def one_switches(row, q):
    """Every signed balanced swap within a paired set of quotient fibres."""
    other = N // q
    fibres = tuple(tuple(next(i for i in range(y, N, q) if i % other == x)
                         for x in range(other)) for y in range(q))
    for left, right in combinations(fibres, 2):
        matched = {-1: [], 1: []}
        for i, j in zip(left, right, strict=True):
            if row[i] and row[i] == -row[j]:
                matched[row[i]].append((1 << i) | (1 << j))
        for count in range(1, min(map(len, matched.values())) + 1):
            negative = combinations(matched[-1], count)
            positive = combinations(matched[1], count)
            for a, b in product(negative, positive):
                yield sum(a + b)


def signed_balance(row, mask):
    return all(sum(value for i, value in enumerate(row) if mask >> i & 1 and i % q == j) == 0
               for q in (13, 23) for j in range(q))


def verify_fixture(anchor, negative, decks, index, changes, metrics, mod32, mod64, q7):
    positive = tuple(tuple(-x if bits >> j & 1 else x for j, x in enumerate(row))
                     for row, bits in zip(anchor, changes, strict=True))
    for r, (row, mask, choices) in enumerate(zip(anchor, changes, decks, strict=True)):
        assert all(not (mask >> j & 1) or value for j, value in enumerate(row))
        assert signed_balance(row, mask)
        if r == index:
            assert any(a ^ mask in choices and signed_balance(row, a & (a ^ mask))
                       for a in choices)
        else:
            assert mask in choices
    assert tuple(map(sum, positive)) == (0, 1, 0, 0)
    residual = replay(positive, negative, metrics, mod32, 6)
    assert 1 + 2 * sum(value % 8 == 0 for value in residual[1:]) == mod64
    assert check_primitive_norm(positive, residual, primitive_factor(7)) == q7
    print(f"Peak-48 witness {metrics[0]} mod16, {metrics[1]} exact, "
          f"mod7 primitive remainder has {q7} nonzero entries.", flush=True)


def check_field(anchor, decks):
    payload = []
    for row, bank in zip(anchor, decks, strict=True):
        payload.extend((" ".join(map(str, row)), str(len(bank))))
        payload.extend(" ".join(str(mask >> (64 * j) & LIMB) for j in range(5))
                       for mask in sorted(bank))
    with tempfile.TemporaryDirectory() as path:
        binary = Path(path) / "paired_fibres"
        compiler = os.environ.get("CXX", "g++")
        cpp = Path(__file__).with_suffix(".cpp")
        subprocess.run([compiler, "-std=c++20", "-O3", str(cpp), "-o", str(binary)], check=True)
        result = subprocess.run([binary], input="\n".join(payload), text=True,
                                capture_output=True, check=True)
    check = (
        "single 1015968 924479 0 0",
        "double 0 55994653 14247 63000 0",
        "double 1 152120403 47646 116816 0",
    )
    assert tuple(result.stdout.splitlines()) == check
    print(result.stdout, end="")


def main():
    anchor, negative = dual_words(PEAK48_MASKS), nested_negative_words()
    assert periodic(negative) == [599] + [0] * (N - 1)
    replay(anchor, negative, (317, 77, 48, 215552), 145, 6)
    decks = tuple({0} | set(one_switches(row, 13)) | set(one_switches(row, 23))
                  for row in anchor)
    assert tuple(map(len, decks)) == (10583, 17443, 53, 96)
    verify_fixture(anchor, negative, decks, 0, FIRST_DOUBLED,
                   (357, 109, 48, 290816), 193, 109, 109)
    verify_fixture(anchor, negative, decks, 1, SECOND_DOUBLED,
                   (325, 113, 48, 292864), 185, 113, 114)
    check_field(anchor, decks)


if __name__ == "__main__":
    main()
