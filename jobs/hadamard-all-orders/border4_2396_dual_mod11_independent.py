"""Exhaust the four independent reflection axes with integer margin preservation."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from border4_2396 import periodic
from border4_2396_dual_quotient import LOW_AMPLITUDE_MOD16, dual_words, replay
from border4_2396_nested import nested_negative_words


def main():
    s = dual_words(LOW_AMPLITUDE_MOD16)
    t = nested_negative_words()
    assert periodic(t) == [599] + [0] * 298
    assert tuple(map(sum, s)) == (0, 1, 0, 0)
    replay(s, t, (477, 113, 80, 652800), 253, 10)

    compiler = os.environ.get("CXX", "g++")
    if not shutil.which(compiler):
        raise SystemExit(f"Cannot find a C++20 compiler named {compiler}. Set CXX to its path.")
    source = Path(__file__).with_suffix(".cpp")
    rows = "\n".join(" ".join(map(str, row)) for row in s)
    with tempfile.TemporaryDirectory() as path:
        executable = Path(path) / "reflection_check"
        subprocess.run([compiler, "-O3", "-std=c++20", str(source), "-o", str(executable)], check=True)
        subprocess.run([str(executable)], input=rows, text=True, check=True)


if __name__ == "__main__":
    main()
