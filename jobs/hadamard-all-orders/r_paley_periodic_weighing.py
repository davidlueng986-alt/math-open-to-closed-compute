"""Replay the weighing-matrix basis restriction for periodic far words."""

from itertools import combinations
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from r_paley_far_family import quaternion_basis
from r_paley_far_periodic import raw_word, row_fibres
from verify import goethals_seidel, length_299_words


def signs(height, columns):
    return [tuple(2 * (col >> r & 1) - 1 for col in columns) for r in range(height)]


def dot(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True))


def gram_check(columns, other, diagonal):
    return all(dot(a, b) == (diagonal if i == j else 0)
               for i, a in enumerate(columns) for j, b in enumerate(other))


def data():
    words = length_299_words()
    units = [quaternion_basis(*(word[13 * (16 * y % 23)] for word in words)) for y in range(23)]
    assert all(units[y][0] == units[-y % 23][0] for y in range(23))
    first, second = (
        signs(92, goethals_seidel([tuple(row[k][i] for row in units) for i in range(4)]))
        for k in (0, 1)
    )
    d = [tuple((x + y) // 2 for x, y in zip(a, b, strict=True))
         for a, b in zip(first, second, strict=True)]
    e = [tuple((x - y) // 2 for x, y in zip(a, b, strict=True))
         for a, b in zip(first, second, strict=True)]
    g = [tuple(5 * x + y for x, y in zip(a, b, strict=True))
         for a, b in zip(d, e, strict=True)]
    dc, ec = tuple(zip(*d)), tuple(zip(*e))
    assert gram_check(dc, dc, 46) and gram_check(ec, ec, 46)
    assert all(abs(x) + abs(y) == 1 for a, b in zip(d, e, strict=True)
               for x, y in zip(a, b, strict=True))
    assert all(dot(a, b) == -dot(c, f) for i, (a, c) in enumerate(zip(dc, ec, strict=True))
               for b, f in zip(ec[:i+1], dc[:i+1], strict=True))
    rows = [(b ^ 1) * 23 + (r if b < 2 else 22 - r) for b in range(4) for r in range(23)]
    cols = [b * 23 + (22 - r if b < 2 else r) for b in range(4) for r in range(23)]
    phase = (-1, 1, 1, -1)
    assert all(e[i][j] == phase[i//23] * d[r][c]
               for i, r in enumerate(rows) for j, c in enumerate(cols))
    source = goethals_seidel(words)
    fibres = row_fibres()
    assert all(g[i][j] == sum(2 * (source[column[0]] >> r & 1) - 1 for r in row)
               for i, row in enumerate(fibres) for j, column in enumerate(fibres))
    q = raw_word(source, fibres)
    raw = tuple(2 * (q >> row[0] & 1) - 1 for row in fibres)
    assert raw == tuple(a + b for a, b in zip(dc[11], dc[34], strict=True))
    return d, e, g, raw


def disjoint_lines(columns):
    lines = []
    for (i, left), (j, right) in combinations(enumerate(columns), 2):
        if any(x and y for x, y in zip(left, right, strict=True)):
            continue
        for phase in (-1, 1):
            q = tuple(x + phase * y for x, y in zip(left, right, strict=True))
            assert all(abs(x) == 1 for x in q)
            lines.append((i, j, phase, q))
    return lines


def verify():
    d, e, g, _ = data()
    gc = tuple(zip(*g))
    line_d = disjoint_lines(tuple(zip(*d)))
    line_e = disjoint_lines(tuple(zip(*e)))
    expected = [(i, j, phase) for i, j in ((11, 34), (57, 80)) for phase in (-1, 1)]
    assert [item[:3] for item in line_d] == [item[:3] for item in line_e] == expected
    eligible_d = [{j for j, col in enumerate(gc) if abs(dot(q, col)) == 2} for *_, q in line_d]
    assert [len(eligible) for eligible in eligible_d] == [49] * 4
    assert max(len(a & b) for a, b in combinations(eligible_d, 2)) == 36
    assert all(sum(abs(dot(q, col)) == 2 for col in gc) < 47 for *_, q in line_e)

    rows = "\n".join(" ".join(map(str, row)) for row in d) + "\n"
    worker = Path(__file__).with_suffix(".cpp")
    with TemporaryDirectory() as temp:
        executable = Path(temp) / "weighing"
        subprocess.run(["g++", "-O3", "-std=c++17", str(worker), "-o", str(executable)],
                       check=True)
        result = subprocess.run([str(executable)], input=rows, text=True, check=True,
                                capture_output=True).stdout.strip()
    assert result.splitlines() == [
        "5 columns: 49177128 sets, 2768 stopping sets, all full rank modulo 23",
        "6 columns: 713068356 sets, 1526544 stopping sets, all full rank modulo 23",
    ]
    print("Paley periodic weighing: all sets of at most six axes independent modulo 23")
    print(result)


if __name__ == "__main__":
    verify()
