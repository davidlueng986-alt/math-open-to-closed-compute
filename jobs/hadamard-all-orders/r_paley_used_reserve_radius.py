"""Replay paired-moment near-reserve exclusions on the fixed 1215-column frame."""

import json
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from r_paley_bucket_extension import SELECTED
from r_paley_periodic_skew import DATA
from verify import goethals_seidel, length_299_words, rows_from_columns


def inputs():
    m = 1196
    old = next(r for r in json.loads(DATA.read_text(encoding="ascii"))["extensions"]
               if r["width"] == 1214)
    rows = old["inner_rows"] + [319]
    pivots = old["inner_columns"] + [344]
    selected = [j for j in range(m) if SELECTED >> j & 1]
    assert len(set(rows)) == len(set(pivots)) == 15
    assert len(selected) == 600 and not set(pivots).intersection(selected)
    full = goethals_seidel(length_299_words())
    source_rows = rows_from_columns(m, full)
    pieces = [" ".join(map(str, rows)), " ".join(map(str, pivots)), " ".join(map(str, selected))]
    pieces.extend(f"{word:0{m}b}"[::-1] for word in source_rows)
    return "\n".join(pieces) + "\n"


def verify():
    source = Path(__file__).with_suffix(".cpp")
    with TemporaryDirectory() as path:
        binary = Path(path) / "used_reserve_radius"
        run(["c++", "-std=c++17", "-O3", "-march=native", str(source), "-o", str(binary)], check=True)
        run([str(binary)], input=inputs(), text=True, check=True)


if __name__ == "__main__":
    verify()
