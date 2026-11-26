"""Replay two additional scoped exclusions for the double-far sources."""

from itertools import combinations
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from r_paley_double_far import build_pair, build_source, fibres, dot
from r_paley_double_far_family import compressed_data
from r_paley_double_far_periodic import channel_data
from r_paley_periodic_partner import dot as vector_dot, integer_rows, nary
from verify import goethals_seidel, rows_from_columns


def check_symmetric(even, run):
    source = build_source()
    raw, _ = build_pair(source)
    group = fibres()
    chosen = [col for col in group if all(abs(dot(word, source[col[0]])) == 2 for word in raw)]
    assert len(chosen) == 32
    masks = [sum(1 << j for j in col) for col in chosen]
    for row in rows_from_columns(1196, source):
        assert all(abs(2 * (row & mask).bit_count() - 23) <= 9 for mask in masks)
    assert run("symmetric", integer_rows(even)) == ["symmetric 3602435 0"]
    print("Paley double-far extensions: 3602435 symmetric one-flip keys, no precursor")



def check_mixed(odd, even, run):
    output = run("odd", integer_rows(odd))
    assert output[-1] == "odd 1785086629 94"
    lines = set()
    for line in output[:-1]:
        label, a, b = line.split()
        assert label == "line"
        word = tuple(v - 1 for v in nary(int(a), 3, 12) + nary(int(b), 3, 12))
        assert next(v for v in word if v) == 1
        lines.add(word)
    assert len(lines) == 94
    batches = []
    for line in sorted(lines):
        p = tuple(vector_dot(line, col) for col in zip(*odd))
        costs = tuple(7 * abs(x) if abs(x) <= 2 else 23 for x in p)
        assert sum(costs[:8]) <= 68 and sum(costs[8:]) <= 68
        matrix = [even[i] for i, x in enumerate(line) if not x] + even[24:]
        batches.append(integer_rows([(len(matrix),), p, *matrix]))
    assert run("mixed", str(len(batches)) + "\n" + "".join(batches)) == ["mixed 14157980 0"]
    print("Paley double-far extensions: 1785086629 odd keys, 94 candidate directions")
    print("Paley double-far extensions: 14157980 even keys, no one-flip precursor")


def check_family(run):
    _, units, coeff = compressed_data()
    bases = [
        goethals_seidel([tuple(row[u][j] for row in units) for j in range(4)])
        for u in range(4)
    ]
    for left, right in combinations(bases, 2):
        assert all((a ^ b).bit_count() == 26 for a, b in zip(left, right, strict=True))
    joined = [
        j for j in range(52) if all(entry[j][1] == 0 and abs(entry[j][0]) == 2 for entry in coeff)
    ]
    same = [j for j in joined if coeff[0][j][0] == coeff[1][j][0]]
    opposite = [j for j in joined if coeff[0][j][0] == -coeff[1][j][0]]
    assert len(same) == len(opposite) == 16
    columns = [tuple(h[j] for h in bases) for j in same + opposite]
    assert run("family", integer_rows(columns)) == [
        "family 23 36133760 6019616 6019616 0 0",
        "family 24 2459392 540928 540928 0 0",
        "family 25 84864 26144 26144 0 0",
        "family 26 832 384 384 0 0",
    ]
    print("Paley double-far extensions: no third period-13 line for family |s| >= 23")


def verify():
    _, _, _, _, odd, even = channel_data()
    worker = Path(__file__).with_suffix(".cpp")
    with TemporaryDirectory() as temp:
        exe = Path(temp) / "double-far-extensions"
        subprocess.run(["g++", "-O3", "-std=c++17", str(worker), "-o", str(exe)], check=True)

        def run(mode, inp):
            return subprocess.run([str(exe), mode], input=inp, text=True, check=True,
                                  capture_output=True).stdout.splitlines()

        check_symmetric(even, run)
        check_mixed(odd, even, run)
        check_family(run)


if __name__ == "__main__":
    verify()
