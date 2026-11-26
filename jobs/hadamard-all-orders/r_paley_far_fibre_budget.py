"""Reconstruct the physical fibre means and replay their exact omission bounds."""

from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from r_paley_far_periodic import raw_word, row_fibres
from verify import goethals_seidel, length_299_words


def profiles():
    m = 1196
    source = goethals_seidel(length_299_words())
    fibres = row_fibres()
    z = raw_word(source, fibres)
    projections = [m - 2 * (z ^ word).bit_count() for word in source]
    columns = [group for group in fibres if abs(projections[group[0]]) == 2]
    assert len(fibres) == 92 and len(columns) == 49
    assert sum(abs(p) == 2 for p in projections) == 637

    out = []
    for f in fibres:
        coefficients = []
        for group in columns:
            assert all(projections[j] == projections[group[0]] for j in group)
            term = projections[group[0]] // 2
            sums = [sum(term * (-1 if (z ^ source[j]) >> r & 1 else 1) for j in group)
                    for r in f]
            assert len(set(sums)) == 1 and abs(sums[0]) in (1, 5)
            coefficients.append(sums[0])
        out.append(" ".join(map(str, coefficients)))
    return "\n".join(out) + "\n"


def verify():
    source = Path(__file__).with_suffix(".cpp")
    with TemporaryDirectory() as path:
        binary = Path(path) / "fibre_budget"
        run(["c++", "-std=c++17", "-O3", str(source), "-o", str(binary)], check=True)
        run([str(binary)], input=profiles(), text=True, check=True)


if __name__ == "__main__":
    verify()
