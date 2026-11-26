"""Rebuild the nested source and check the small-first-swap obstruction."""

from pathlib import Path
import subprocess
import tempfile

from border4_2396 import periodic
from border4_2396_exact_negative import word
from border4_2396_fixed_first import TARGET, quotient, reflect
from border4_2396_nested import NEAR_C13, nested_negative_words


def verify():
    negative = nested_negative_words()
    positive = tuple(map(word, NEAR_C13))
    assert all(x * x + y * y == 1
               for a, b in zip(positive, negative, strict=True)
               for x, y in zip(a, b, strict=True))
    assert tuple(sum(map(abs, row)) for row in positive) == (164, 173, 130, 130)
    assert tuple(map(sum, positive)) == (0, 1, 0, 0)
    assert periodic(negative) == [599] + [0] * 298
    positive_correlation = periodic(positive)
    assert positive_correlation[0] == 597
    assert all((v + 2) % 8 == 0 for v in positive_correlation[1:])
    assert [v - goal for v, goal in zip(quotient(positive), TARGET, strict=True)] == (
        [0, 0, 0, -8, 8, 0, 0, 0, 0, 8, -8, 0, 0]
    )
    source = "".join(
        " ".join(map(str, row)) + "\n"
        for row in positive[:3] + (reflect(positive[3]),)
    )
    checker = Path(__file__).with_suffix(".cpp")
    with tempfile.TemporaryDirectory() as directory:
        binary = Path(directory) / "border4_2396_small_first"
        subprocess.run(["g++", "-O3", "-std=c++20", str(checker), "-o", str(binary)], check=True)
        subprocess.run([str(binary)], input=source, text=True, check=True)


if __name__ == "__main__":
    verify()
